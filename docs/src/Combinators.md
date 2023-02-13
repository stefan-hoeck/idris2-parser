# Parser Combinators

```idris
module Combinators

import Derive.Prelude
import Text.Bounded
import Language.JSON.Lexer
import Profile
import System
import Text.Lex
import Text.Parse

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
  interpolate (Lit x)  = "'\{show x}'"
  interpolate Space = "<spaces>"

public export
data JSErr : Type where
  ExpectedString  : JSErr

%runElab derive "JSErr" [Show,Eq]

export
Interpolation JSErr where
  interpolate ExpectedString  = "Expected string literal"

public export %tcinline
0 JSParseErr : Type
JSParseErr = ParseError JSToken JSErr

strLit : SnocList Char -> JSToken
strLit = Lit . JString . cast

str : SnocList Char -> AutoTok Char JSToken
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
str sc (c    :: xs) = str (sc :< c) xs
str sc []           = failEOI p

export
tok : Tok Char JSToken
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
tok xs                           = Lit . JNumber <$> double xs
```

## Lexing with Combinators

```idris
jsonTokenMap : TokenMap Char JSToken
jsonTokenMap =
  [ (spaces, const Space)
  , (is ',', const ',')
  , (is ':', const ':')
  , (is '[', const ':')
  , (is ']', const ':')
  , (is '{', const ':')
  , (is '}', const ':')
  , (exact "null", const $ Lit JNull)
  , (exact "true", const $ Lit (JBool True))
  , (exact "false", const $ Lit (JBool True))
  , (doubleLit, Lit . JNumber . cast . cast {to = String})
  , (stringLit, Lit . JString . cast)
  ]

jsonStr : String
jsonStr = #"{"tree":{"name":true,"kids":[{"name":false,"kids":[{"name":null,"kids":[{"name":"pkg","kids":[{"name":"exp","kids":[{"name":"draw","kids":[{"name":"Makefile","kids":[],"cl_weight":1,"touches":1,"min_t":1258062920,"max_t":1258062920,"mean_t":1258062920}],"cl_weight":1,"touches":1,"min_t":1258062920,"max_t":1258062920,"mean_t":1258062920}],"cl_weight":2,"touches":2,"min_t":1258062920,"max_t":1316289444,"mean_t":1287176182}],"cl_weight":172.302597402597,"touches":174,"min_t":1254251724,"max_t":1316289444,"mean_t":1283150599}],"cl_weight":176.4999999999996,"touches":177,"min_t":1254251724,"max_t":1316289444,"mean_t":1282723881},{"name":"misc","kids":[],"cl_weight":3,"touches":3,"min_t":1255542979,"max_t":1264539389,"mean_t":1261000371},{"name":"doc","kids":[{"name":"effective_go.html","kids":[],"cl_weight":1,"touches":1,"min_t":1258401378,"max_t":1258401378,"mean_t":1258401378},{"name":"install.html","kids":[],"cl_weight":1,"touches":1,"min_t":1257967097,"max_t":1257967097,"mean_t":1257967097},{"name":"go-logo-black.png","kids":[],"cl_weight":0.2,"touches":1,"min_t":1257452334,"max_t":1257452334,"mean_t":1257452334},{"name":"video-snap.jpg","kids":[],"cl_weight":0.2,"touches":1,"min_t":1257452334,"max_t":1257452334,"mean_t":1257452334},{"name":"root.html","kids":[],"cl_weight":0.45,"touches":2,"min_t":1257307185,"max_t":1257452334,"mean_t":1257379759},{"name":"style.css","kids":[],"cl_weight":0.45,"touches":2,"min_t":1257307185,"max_t":1257452334,"mean_t":1257379759},{"name":"go-logo-blue.png","kids":[],"cl_weight":0.25,"touches":1,"min_t":1257307185,"max_t":1257307185,"mean_t":1257307185}],"cl_weight":3.5500000000000007,"touches":4,"min_t":1257307185,"max_t":1258401378,"mean_t":1257781998},{"name":"lib","kids":[{"name":"godoc","kids":[{"name":"godoc.html","kids":[],"cl_weight":0.45,"touches":2,"min_t":1257307185,"max_t":1257452334,"mean_t":1257379759}],"cl_weight":0.45,"touches":2,"min_t":1257307185,"max_t":1257452334,"mean_t":1257379759}],"cl_weight":0.45,"touches":2,"min_t":1257307185,"max_t":1257452334,"mean_t":1257379759}],"cl_weight":0,"touches":0,"min_t":0,"max_t":0,"mean_t":0}],"cl_weight":0,"touches":0,"min_t":0,"max_t":0,"mean_t":0},"username":"agl"}"#

bench : Benchmark Void
bench = Group "lexer" [
  Group "digits" [
      Single "manual"     (basic (singleLineDropSpaces tok) jsonStr)
    , Single "combinator" (basic (multiline $ first jsonTokenMap) jsonStr)
    , Single "contrib"    (basic lexJSON jsonStr)
    ]
  ]

fromArgs : List String -> String -> Bool
fromArgs [_,p] = case split ('=' ==) p of
  "--only" ::: [s] => isInfixOf s
  _                => const False
fromArgs _ = const True

main : IO ()
main = do
  select <- fromArgs <$> getArgs
  runDefault select Table show bench
```

<!-- vi: filetype=idris2:syntax=markdown
-->