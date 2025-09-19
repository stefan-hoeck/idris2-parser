# Parser Combinators

"Who in their right mind would write a lexer or parser
from scratch? And by the way, your toy language of arithmetic
expressions was unrealistically trivial!"
That's probably correct, so we are going to
write a [JSON](https://www.json.org/json-en.html) parser in this section.
That's still not a very complex grammar, but it will allow us
to dive into combinators for lexing and parsing.

We are first going to define the necessary data types: A tree structure
representing the JSON data, a token type, plus a type for custom
error messages:

```idris
module Combinators

import Data.List1
import Derive.Prelude
import Text.Lex
import Text.Parse
import Text.Parse.Manual
import Profile

%default total
%language ElabReflection

public export
data JsonTree : Type where
  JNull   : JsonTree
  JNumber : Double -> JsonTree
  JBool   : Bool   -> JsonTree
  JString : String -> JsonTree
  JArray  : List JsonTree -> JsonTree
  JObject : List (String, JsonTree) -> JsonTree

%runElab derive "JsonTree" [Show,Eq]

public export
data JSToken : Type where
  Symbol   : Char -> JSToken
  Lit      : JsonTree -> JSToken
  Space    : JSToken

%runElab derive "JSToken" [Show,Eq]

public export %inline
fromChar : Char -> JSToken
fromChar = Symbol

export
Interpolation JSToken where
  interpolate (Symbol c) = show c
  interpolate (Lit x)    = "'\{show x}'"
  interpolate Space      = "<spaces>"

public export
data JSErr : Type where
  ExpectedString  : JSErr

%runElab derive "JSErr" [Show,Eq]

export
Interpolation JSErr where
  interpolate ExpectedString  = "Expected string literal"

public export %tcinline
0 JSParseErr : Type
JSParseErr = InnerError JSErr
```

## A Manually written Lexer

We begin with the most notorious aspect of lexing JSON
data: String literals. And we are not going to skip over the
gory details this time. A JSON string can contain any unicode character
with the exception of certain control and space characters
and quotes, which must be escaped. This is handled in the
following function for lexing a string literal:

```idris
strLit : SnocList Char -> JSToken
strLit = Lit . JString . cast

str : SnocList Char -> AutoTok e JSToken
str sc ('\\' :: c  :: xs) = case c of
  '"'  => str (sc :< '"') xs
  'n'  => str (sc :< '\n') xs
  'f'  => str (sc :< '\f') xs
  'b'  => str (sc :< '\b') xs
  'r'  => str (sc :< '\r') xs
  't'  => str (sc :< '\t') xs
  '\\' => str (sc :< '\\') xs
  '/'  => str (sc :< '/') xs
  'u'  => case xs of
    w :: x :: y :: z :: t' =>
      if isHexDigit w && isHexDigit x && isHexDigit y && isHexDigit z
        then
          let c := cast $ hexDigit w * 0x1000 +
                          hexDigit x * 0x100 +
                          hexDigit y * 0x10 +
                          hexDigit z 
           in str (sc :< c) t'
        else invalidEscape p t'
    _    => invalidEscape p xs
  _    => invalidEscape p (c::xs)
str sc ('"'  :: xs) = Succ (strLit sc) xs
str sc (c    :: xs) =
  if isControl c then range (InvalidControl c) p xs
  else str (sc :< c) xs
str sc []           = eoiAt p
```

The most important new thing here is the `AutoTok e JSToken`
type. This `AutoTok` is an alias for the following function type:

```repl
Combinators> :printdef AutoTok
0 Text.Lex.Manual : Type -> Type -> Type
AutoTok e a = (xs : List Char) -> Suffix True xs orig => LexRes True orig e a
```

We use this to automatically keep track of the number of
characters consumed (handled by the `Suffix True xs orig` auto implicit
argument), and we expect that at least one character has already
been consumed when invoking `str`, which makes sense since
we already dropped the opening quotation character (`'"'`).

There is a second non-trivial aspect: Lexing floating point literals.
This functionality is already available in module `Text.SuffixRes`, but
I'm going to reimplement it here to compare it to a corresponding
lexer built from combinators in the next section. For this, we
are going to use a `Shifter`: A function type that takes items
from the head of a list and appends them to a `SnocList`:

```repl
Parser> :printdef Shifter
0 Text.ShiftRes.Shifter : Bool -> Type -> Type
Shifter b t = (st : SnocList t) -> (ts : List t) -> ShiftRes b t st ts
```

It comes with its own predicate defined in `Data.List.Shift`, which
relates an original `SnocList` and `List` with the current
`SnocList` and `List`, proofing not only, that a finite number of
items have been moved but also, that no item was lost and their
order has not changed. It is the core concept used for implementing
the lexer combinators in `Text.Lex.Core`.


```idris
-- A shifter that moves digits.
digs : AutoShift False
digs (x :: xs) = if isDigit x then digs xs else Succ (x::xs)
digs []        = Succ []

-- A strict version of `digs`.
digs1 : AutoShift True
digs1 (x :: xs) = if isDigit x then digs xs else unknownRange sh xs
digs1 []        = eoiAt sh

-- A shifter that moves an integer prefix
integer : AutoShift True
integer ('-' :: xs) = digs1 {b} xs
integer ('+' :: xs) = digs1 {b} xs
integer xs          = digs1 {b} xs

dot,rest,digs0,exp : AutoShift False
exp ('e' :: xs) = weakens $ integer {b} xs
exp ('E' :: xs) = weakens $ integer {b} xs
exp xs          = Succ xs

dot (x :: xs) = if isDigit x then dot xs else exp (x::xs)
dot []        = Succ []

rest ('.'::x::xs) = if isDigit x then dot xs else failDigit Dec (shift sh)
rest ('.'::[])    = eoiAt (shift sh)
rest xs           = exp xs

digs0 (x :: xs) = if isDigit x then digs0 xs else rest (x::xs)
digs0 []        = Succ []

-- A shifter for recognizing JSON numbers
num : Shifter True
num sc ('-' :: '0' :: xs) = rest xs
num sc ('-' :: x   :: xs) =
  if isDigit x then digs0 xs else failDigit Dec (shift Same)
num sc ('0'        :: xs) = rest xs
num sc (x          :: xs) = if isDigit x then digs0 xs else failDigit Dec Same
num sc []                 = eoiAt Same

dbl : Tok True e JSToken
dbl cs = suffix (Lit . JNumber . cast . cast {to = String}) $ num [<] cs
```

That's certainly quite a lot of code just for lexing numbers,
and it's probably the best example of a lexeme where using
a library of combinators makes the code much nicer.
Compared to this, the rest is very simple:

```idris
tok : Tok True e JSToken
tok (','::xs)                    = Succ ',' xs
tok ('"'::xs)                    = str [<] xs
tok (':'::xs)                    = Succ ':' xs
tok ('['::xs)                    = Succ '[' xs
tok (']'::xs)                    = Succ ']' xs
tok ('{'::xs)                    = Succ '{' xs
tok ('}'::xs)                    = Succ '}' xs
tok ('n':: 'u'::'l'::'l'::t)     = Succ (Lit JNull) t
tok ('t'::'r'::'u'::'e'::t)      = Succ (Lit $ JBool True) t
tok ('f'::'a'::'l'::'s'::'e'::t) = Succ (Lit $ JBool False) t
tok xs                           = dbl xs

tokJSON : String -> Either (ParseError Void) (List $ Bounded JSToken)
tokJSON s= mapFst (toParseError Virtual s) $ singleLineDropSpaces tok s
```

## Lexing with Combinators

Below, I implemented a JSON lexer with the combinators
found in `Text.Lex.Core` and `Text.Lex.Util`, both of which are
reexported by `Text.Lex`.

```idris
numberLit : Lexer
numberLit
  = let sign  = is '-'
        whole = is '0' <|> range '1' '9' <+> many digit
        frac  = is '.' <+> digits
        exp   = like 'e' <+> opt (oneOf ['+','-']) <+> digits in
        opt sign <+> whole <+> opt frac <+> opt exp

jsstring : Lexer
jsstring = quote (is '"') jsonChar
  where
    jsonChar : Lexer
    jsonChar =
          (is '\\' <+> oneOf ['\\','"','n','f','b','r','t','/'])
      <|> (exact "\\u" <+> exactly 4 (pred isHexDigit))
      <|> non (pred isControl <|> is '"' <|> is '\\')
```

Compared to these two lexers, the rest is very simple. All
we have to do is to collect the lexers in a `TokenMap`,
where lexers are paired with functions for converting the
corresponding lexemes to values of type `JSToken`:

```idris
jsonTokenMap : TokenMap JSToken
jsonTokenMap =
  [ (spaces, const Space)
  , (is ',', const ',')
  , (is ':', const ':')
  , (is '[', const '[')
  , (is ']', const ']')
  , (is '{', const '{')
  , (is '}', const '}')
  , (exact "null", const $ Lit JNull)
  , (exact "true", const $ Lit (JBool True))
  , (exact "false", const $ Lit (JBool False))
  , (numberLit, Lit . JNumber . cast . cast {to = String})
  , (jsstring, Lit . JString . cast)
  ]

tokJSON2 : String -> Either (ParseError Void) (List $ Bounded JSToken)
tokJSON2 s =
  mapFst (toParseError Virtual s) $ lexManual (first jsonTokenMap) s
```

## Comparing the two Lexers

While I definitely prefer `numberLit` over the manually written
lexer, I'm less sure about `jsstring`: This does not yet convert
any escaped characters, and hence, a function like `str` would
still have to be implemented, although we'd be able to drop
some of the checks in there.

Let us test the two tokenizers at the REPL using the following
utility functions:

```idris
lexAndPrint : String -> IO ()
lexAndPrint s = putStrLn $ either interpolate show (tokJSON s)

lexAndPrint2 : String -> IO ()
lexAndPrint2 s = putStrLn $ either interpolate show (tokJSON2 s)
```

We are mainly interested in how informative the error messages
are in case of a lexing error. We will first look at an example
of an invalid number:

```repl
Combinators> :exec lexAndPrint "{\"foo\":12.e1}"
Error: Unknown token

virtual: 1:8--1:12
 1 | {"foo":12.e1}
            ^^^^

Combinators> :exec lexAndPrint2 "{\"foo\":12.e1}"
Error: Unknown token

virtual: 1:10--1:11
 1 | {"foo":12.e1}
              ^
```

Both errors are similarly expressive: They both show where the lexer
stopped. I tend to find the first version slightly more useful,
because it shows, that the lexer tried to read the invalid `e`
character as part of a longer number literal.

In the next example, we look at two cases of invalid string
literals:

```repl
Combinators> :exec lexAndPrint "{\"foo\":\"bar\tbaz\"}"
Error: Invalid control character: '\t'

virtual: 1:12--1:13
 1 | {"foo":"bar        baz"}
                ^

Combinators> :exec lexAndPrint2 "{\"foo\":\"bar\tbaz\"}"
Error: Unknown token

virtual: 1:12--1:13
 1 | {"foo":"bar        baz"}
                ^

Combinators> :exec lexAndPrint "{\"foo\":\"bar\\u001 baz\"}"
Error: Invalid escape sequence

virtual: 1:12--1:18
 1 | {"foo":"bar\u001 baz"}
                ^^^^^^

Combinators> :exec lexAndPrint2 "{\"foo\":\"bar\\u001 baz\"}"
Error: Unknown token

virtual: 1:12--1:13
 1 | {"foo":"bar\u001 baz"}
                ^
```

In this case, the hand written lexer is clearly superior:
It not only marks the whole erroneous escape sequence in the second
example, it also gives a clearer message in case of the tab
character that was part of the string literal.

## Parsing: Manual and with Combinators

Most of the complexity of parsing JSON is already being taken care of
by the lexers. The only thing missing is the recursive building of the
JSON tree values.

```idris
0 Rule : Bool -> Type -> Type
Rule b t =
     (xs : List $ Bounded JSToken)
  -> (0 acc : SuffixAcc xs)
  -> Res b JSToken xs JSErr t

array : Bounds -> SnocList JsonTree -> Rule True JsonTree

object : Bounds -> SnocList (String,JsonTree) -> Rule True JsonTree

value : Rule True JsonTree
value (B (Lit y) _ :: xs)        _      = Succ0 y xs
value (B '[' _ :: B ']' _ :: xs) _      = Succ0 (JArray []) xs
value (B '[' b :: xs)            (SA r) = succT $ array b [<] xs r
value (B '{' _ :: B '}' _ :: xs) _      = Succ0 (JObject []) xs
value (B '{' b :: xs)            (SA r) = succT $ object b [<] xs r
value xs                         _      = fail xs

array b sv xs sa@(SA r) = case value xs sa of
  Succ0 v (B ',' _ :: ys) => succT $ array b (sv :< v) ys r
  Succ0 v (B ']' _ :: ys) => Succ0 (JArray $ sv <>> [v]) ys
  res                     => failInParen b '[' res

object b sv (B (Lit $ JString l) _ :: B ':' _ :: xs) (SA r) =
  case succT $ value xs r of
    Succ0 v (B ',' _ :: ys) => succT $ object b (sv :< (l,v)) ys r
    Succ0 v (B '}' _ :: ys) => Succ0 (JObject $ sv <>> [(l,v)]) ys
    res                     => failInParen b '{' res
object b sv (B (Lit $ JString s) _ :: x :: xs) _ = expected x.bounds ":" "\{s}"
object b sv (x :: xs)                          _ = custom x.bounds ExpectedString
object b sv []                                 _ = eoi
```

The above is not too bad: The parser is simple enough to understand
pretty quickly what's going on. Below, I'm going to implement a
JSON parser using the parser combinators from `Text.Parse.Core`.

```idris
0 Rule2 : Bool -> Type -> Type
Rule2 b t = Grammar b () JSToken JSErr t

covering
array2 : Rule2 True JsonTree

covering
object2 : Rule2 True JsonTree

lit : Rule2 True JsonTree
lit = terminal $ \case Lit j => Just j; _ => Nothing

jstring : Rule2 True String
jstring = terminal $ \case Lit (JString s) => Just s; _ => Nothing

covering
value2 : Rule2 True JsonTree
value2 = lit <|> array2 <|> object2

array2 = JArray <$> between (is '[') (is ']') (sepBy (is ',') value2)

covering
pair2 : Rule2 True (String,JsonTree)
pair2 = [| MkPair jstring (is ':' >> value2) |]

object2 = JObject <$> between (is '{') (is '}') (sepBy (is ',') pair2)
```

This is indeed very short and concise. Unfortunately, it is not accepted
by the totality checker, even though the `Grammar` data type was
explicitly designed for handling such mutually recursive
parsers. The same weakness can be experienced when using the
parser combinators from *contrib* or the Idris compiler API.


Below are some utility function for experimenting with the
two parsers we implemented in this section. Both work reasonably
well and give reasonable error messages most of the time. In both
cases it should be possible to give more precise errors in certain
circumstances, although this might be easier to get right in
the hand-written case.

```idris
parse1 : String -> Either (ParseError JSErr) JsonTree
parse1 s = case tokJSON s of
  Left x  => Left $ {error $= fromVoid} x
  Right x => result Virtual s $ value x suffixAcc

covering
parse2 : String -> Either (List1 (ParseError JSErr)) JsonTree
parse2 s = case tokJSON2 s of
  Left x  => Left (singleton $ {error $= fromVoid} x)
  Right x => case parse value2 () x of
    Left es                => Left (toParseError Virtual s <$> es)
    Right ((),res,[])      => Right res
    Right ((),res,(x::xs)) =>
      Left (singleton $ toParseError Virtual s $ Expected [] . interpolate <$> x)

testParse1 : String -> IO ()
testParse1 s = putStrLn $ either interpolate show (parse1 s)

covering
testParse2 : String -> IO ()
testParse2 s =
  case parse2 s of
    Left xs => traverse_ (putStrLn . interpolate) xs
    Right v => printLn v
```

## Performance

Below is a small program and example JSON string for profiling the two
lexers and parsers. And here we observe a significant difference, especially
with the lexers: The manually written lexer is a order of magnitude
faster, especially due to the notoriously slow lexing of string literals.

On my machine, I get the following output when running this module
with pack:

```sh
$ pack -o combs exec docs/src/Combinators.md
[ info ] Found local config at /data/gundi/idris/parser/pack.toml
[ info ] Using package collection nightly-230213
[ info ] Found `.ipkg` file at /data/gundi/idris/parser/docs/docs.ipkg
all/lex/manual                                       43.81 μs   48.83 μs 0.999
all/lex/combinator                                   425.1 μs   430.1 μs 0.998
all/parse/manual                                     46.42 μs   47.07 μs 0.999
all/parse/combinator                                 541.6 μs   551.4 μs 0.999
```

```idris
jsonStr : String
jsonStr = #"{"tree":{"name":true,"kids":[{"name":false,"kids":[{"name":null,"kids":[{"name":"pkg","kids":[{"name":"exp","kids":[{"name":"draw","kids":[{"name":"Makefile","kids":[],"cl_weight":1,"touches":1,"min_t":1258062920,"max_t":1258062920,"mean_t":1258062920}],"cl_weight":1,"touches":1,"min_t":1258062920,"max_t":1258062920,"mean_t":1258062920}],"cl_weight":2,"touches":2,"min_t":1258062920,"max_t":1316289444,"mean_t":1287176182}],"cl_weight":172.302597402597,"touches":174,"min_t":1254251724,"max_t":1316289444,"mean_t":1283150599}],"cl_weight":176.4999999999996,"touches":177,"min_t":1254251724,"max_t":1316289444,"mean_t":1282723881},{"name":"misc","kids":[],"cl_weight":3,"touches":3,"min_t":1255542979,"max_t":1264539389,"mean_t":1261000371},{"name":"doc","kids":[{"name":"effective_go.html","kids":[],"cl_weight":1,"touches":1,"min_t":1258401378,"max_t":1258401378,"mean_t":1258401378},{"name":"install.html","kids":[],"cl_weight":1,"touches":1,"min_t":1257967097,"max_t":1257967097,"mean_t":1257967097},{"name":"go-logo-black.png","kids":[],"cl_weight":0.2,"touches":1,"min_t":1257452334,"max_t":1257452334,"mean_t":1257452334},{"name":"video-snap.jpg","kids":[],"cl_weight":0.2,"touches":1,"min_t":1257452334,"max_t":1257452334,"mean_t":1257452334},{"name":"root.html","kids":[],"cl_weight":0.45,"touches":2,"min_t":1257307185,"max_t":1257452334,"mean_t":1257379759},{"name":"style.css","kids":[],"cl_weight":0.45,"touches":2,"min_t":1257307185,"max_t":1257452334,"mean_t":1257379759},{"name":"go-logo-blue.png","kids":[],"cl_weight":0.25,"touches":1,"min_t":1257307185,"max_t":1257307185,"mean_t":1257307185}],"cl_weight":3.5500000000000007,"touches":4,"min_t":1257307185,"max_t":1258401378,"mean_t":1257781998},{"name":"lib","kids":[{"name":"godoc","kids":[{"name":"godoc.html","kids":[],"cl_weight":0.45,"touches":2,"min_t":1257307185,"max_t":1257452334,"mean_t":1257379759}],"cl_weight":0.45,"touches":2,"min_t":1257307185,"max_t":1257452334,"mean_t":1257379759}],"cl_weight":0.45,"touches":2,"min_t":1257307185,"max_t":1257452334,"mean_t":1257379759}],"cl_weight":0,"touches":0,"min_t":0,"max_t":0,"mean_t":0}],"cl_weight":0,"touches":0,"min_t":0,"max_t":0,"mean_t":0},"username":"agl"}"#

covering
bench : Benchmark Void
bench = Group "all" [
    Group "lex" [
      Single "manual"     (basic tokJSON jsonStr)
    , Single "combinator" (basic tokJSON2 jsonStr)
    ]
  , Group "parse" [
      Single "manual"     (basic parse1 jsonStr)
    , Single "combinator" (basic parse2 jsonStr)
    ]
  ]

covering
main : IO ()
main = runDefault (const True) Table show bench
```

## Conclusion

The goal of this part of the documentation was to give you some
hints for deciding, which method for writing your parsers and lexers
you prefer. I also wanted to show that it is definitely possible
to write fast performing, provably total lexers and parsers by
hand without resorting to combinators. This might even give you
more control about the error messages you get, although everything
might just be a wee more verbose.

I'll yet have to try my hand on a parser of a real programming
language such as Idris itself. It might be interesting to see, how
for we can get with doing everything manually in such a situation.

<!-- vi: filetype=idris2:syntax=markdown
-->
