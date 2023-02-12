# `Suffix`: A new Predicate on `List`

Today, we are going to write a parser for a very small
language of arithmetic operations. Let's go!

```idris
module Intro

import Data.List
import Derive.Prelude
import Text.Parse.Manual

%default total
%language ElabReflection
```

## Syntax and some Types

Our program should be able to parse expressions of the form
`(12 + 7) * 5 * (8 + 2)` accepting only natural numbers as literals,
operators for addition and multiplication, and parentheses for grouping
operators. The usual precedence should apply: Multiplication should have
higher precedence than addition. We allow arbitrary whitespace between
tokens to enhance readability.

First, we define a syntax tree for representing our expressions:

```idris
public export
data Expr : Type where
  Lit  : Nat -> Expr
  Add  : Expr -> Expr -> Expr
  Mult : Expr -> Expr -> Expr

%runElab derive "Expr" [Show,Eq]
```

To make writing expressions at compile time more convenient, we can
implement the `Num` interface:

```idris
public export %inline
Num Expr where
  fromInteger = Lit . fromInteger
  (+) = Add
  (*) = Mult
```

And we can write a function for evaluating expressions:

```idris
public export
eval : Expr -> Nat
eval (Lit k)    = k
eval (Add x y)  = eval x + eval y
eval (Mult x y) = eval x * eval y
```

Let's quickly test, if all is well:

```idris
test1 : eval (7 + 3 * 12) === 43
test1 = Refl
```

## Lexing Expressions

I prefer separating the processes of lexing and parsing for several
reasons: Parsing is complex enough without having to deal with "word-level"
stuff like converting numbers, dealing with different types of whitespace,
and unescaping string literals. In addition, for most non-trivial projects,
it makes sense to annotate the lexemes of a language with bounds, so we
will later on be able to print nice error messages with source locations.

We will therefore first define a data type for the lexical tokens making
up our language:

```idris
public export
data Op = P | M

%runElab derive "Op" [Show,Eq]

public export
data Token : Type where
  TLit : Nat -> Token
  TSym : Char -> Token
  TOp  : Op -> Token

%runElab derive "Token" [Show,Eq]

public export
FromChar Token where
  fromChar '+' = TOp P
  fromChar '*' = TOp M
  fromChar c   = TSym c
```

Now, let us implement a tokenizer for our language. We want to generate
proper error messages from the beginning, so we use `Text.ParseError`,
which comes with some nice pretty printing facilities. This means, that
we will also have to deal with source locations, handled in
`Text.Bounded`. Here's a first take:

```idris
public export
0 Err : Type
Err = ParseError Token Void

lit :
     SnocList (Bounded Token)
  -> (start,cur : Position)
  -> Nat
  -> List Char
  -> Either (Bounded Err) (List $ Bounded Token)

tok :
     SnocList (Bounded Token)
  -> (cur : Position)
  -> List Char
  -> Either (Bounded Err) (List $ Bounded Token)

lit st s c n []        = Right $ st <>> [bounded (TLit n) s c]
lit st s c n (x :: xs) =
  if isDigit x
     then lit st s (incCol c) (n*10 + digit x) xs
     else tok (st :< bounded (TLit n) s c) c (x::xs)

isSymbol : Char -> Bool
isSymbol '(' = True
isSymbol ')' = True
isSymbol '*' = True
isSymbol '+' = True
isSymbol _   = False

tok st c (x :: xs) = 
  if      isSymbol x then tok (st :< oneChar (TSym x) c) (incCol c) xs
  else if isSpace x then tok st (next x c) xs
  else if isDigit x then lit st c (incCol c) (digit x) xs
  else Left (oneChar (Reason UnknownToken) c)
tok st c []        = Right $ st <>> []
```

As you can see, I implemented two mutually recursive function,
each representing a different state in the lexer: `lit` for
lexing a `Nat` literal, `tok` for lexing other tokens.
The code above is not pretty: It contains a significant amount
of repetition, and the manual construction of bounds makes it
rather verbose. On the positive side, it is stack safe, provably
total, and it beats the currently available lexing DSLs from
contrib and the Idris2 API in terms of performance.

Let's have a look at the types and utilities involved:
`Text.Bounded.Position` describes a position (line and column) in a string
as a zero-based pair of natural numbers. `Text.Bounded.Bounds`, a monoid,
wraps a pair of positions to define a range of text in a string,
and `Text.Bounded.Bounded`, pairs a value with the `Bounds`,
correspoding to the text from which it was created. Utilities
`incLine` and `incCol` adjust the current position, and
`oneChar` and `bounded` are smart constructors for `Bounded`.

Let's quickly test our lexer at the command line, by implementing
a simple pretty printer:

```idris
public export
Interpolation Op where
  interpolate P = "+"
  interpolate M = "*"

public export
Interpolation Token where
  interpolate (TLit n) = show n
  interpolate (TSym s) = show s
  interpolate (TOp  s) = interpolate s

printRes : String -> Either (Bounded Err) (List $ Bounded Token) -> String
printRes _ (Right ts) = unlines $ (\(B t bs) => "\{t}: \{bs}") <$> ts
printRes s (Left b) =
  uncurry (printParseError s) (virtualFromBounded b)

lexAndPrint : String -> IO ()
lexAndPrint s = putStrLn $ printRes s (tok [<] begin $ unpack s)
```

Here's a quick REPL session:

```repl
Intro> :exec lexAndPrint "(12 + 100) * 10"
'(': 1:1--1:2
12: 1:2--1:4
'+': 1:5--1:6
100: 1:7--1:10
')': 1:10--1:11
'*': 1:12--1:13
10: 1:14--1:16

Intro> :exec lexAndPrint "(12 + 100) * abc"
Error: Unknown token

virtual: 1:14--1:15
 1 | (12 + 100) * abc
                  ^
```

So, our tokens are pair with proper bounds, and we get
a decent error message in case of invalid input.

## Code reuse?

What was shown above, is of course not a very nice way for writing
a lexer, and it can be quite error prone, since we do everything
manually. For instance, the fact that we have to intertwine
the lexing of literals and symbols makes it impossible to reuse
these functions in other lexers. Let's try and do better. At first,
we drop the handling of bounds and erros. We'll reintroduce those
later. Here are two functions
for taking a single token from the head of a list of characters:

```idris
lit2 : Nat -> List Char -> (List Char, Token)
lit2 k []      = ([], TLit k)
lit2 k (x::xs) = if isDigit x then lit2 (k*10 + digit x) xs else (x::xs, TLit k)

tok2 : (cs : List Char) -> {auto 0 p : NonEmpty cs} -> Maybe (List Char, Token)
tok2 (x :: xs) =
  if      isSymbol x then Just (xs, TSym x)
  else if isDigit x then Just $ lit2 (digit x) xs
  else Nothing
```

This is of course just an explicit state monad with some rudimentary error
handling. However, we face an issue when we try to lex a string of several
tokens:

```idris
failing "toks2 is not total"
  toks2 : SnocList Token -> List Char -> Maybe (List Token)
  toks2 sx []           = Just $ sx <>> []
  toks2 sx ('\n' :: cs) = toks2 sx cs
  toks2 sx ('\t' :: cs) = toks2 sx cs
  toks2 sx (' '  :: cs) = toks2 sx cs
  toks2 sx cs@(_ :: _)  = case tok2 cs of
    Just (cs',t) => toks2 (sx :< t) cs'
    Nothing      => Nothing
```

Idris2 can't verify that function `toks2` is total, because it has no chance
of verifying that our list of characters is getting shorter, and so the
totality checker is not satisfied. This is the very problem we have to
solve when we try to write libraries for provably total lexers and
parser combinators: How can we keep track that our input is getting
strictly shorter and, therefore, our lexers and parser must terminate
after a finite number of computational steps?

Enter `Data.List.Suffix`, a predicate on a pair of lists, proving
that the first list is a suffix of the second:

```idris
suffixSame : Suffix False xs xs
suffixSame = Same

suffixUncons : Suffix True [4,5] [1..5]
suffixUncons = %search
```

As you can see, `Suffix` is indexed by a boolean flag, indicating whether
the first list is a *strict* suffix of the second or not.

Our first task will be to modify function `tok2` in such a way that
it returns a proof the returned list of characters is a strict suffix
of the input:

```idris
data Result : (cs : List Char) -> Type -> Type where
  Yes :
       {0 cs : List Char}
    -> (val : a)
    -> (xs  : List Char)
    -> {auto p : Suffix True xs cs}
    -> Result cs a
  No  : {0 cs : _} -> Result cs a

lit3 : Nat -> (xs : List Char) -> {auto p : Suffix True xs cs} -> Result cs Token
lit3 k []      = Yes (TLit k) []
lit3 k (x::xs) =
  if isDigit x then lit3 (k*10 + digit x) xs else Yes (TLit k) (x::xs)

tok3 : (cs : List Char) -> {auto 0 p : NonEmpty cs} -> Result cs Token
tok3 (x :: xs) =
  if      isSymbol x then Yes (TSym x) xs
  else if isDigit x then lit3 (digit x) xs
  else No
```

The next step will be to use a utility type called `SuffixAcc`, a value
of which is a proof that every sequence of strictly shorter lists of
characters must be finite. This is very similar the concept of
a [well-founded relation](https://en.wikipedia.org/wiki/Well-founded_relation).

```idris
toks3 :
      SnocList Token
  -> (cs : List Char)
  -> (0 acc : SuffixAcc cs)
  -> Maybe (List Token)
toks3 sx []           _      = Just $ sx <>> []
toks3 sx (c :: cs) (SA r) =
  if     isSpace c then toks3 sx cs r
  else case tok3 (c::cs) of
    Yes t cs' => toks3 (sx :< t) cs' r
    No        => Nothing
```

And the totality checker is happy! So, what's going on here?
Our intermediary `Yes` result holds an auto implicit proof
that `cs'` is strictly shorter than `cs`. At the same time
`r` requires exactly such a proof as an auto implicit argument
to construct a value of type `SuffixAcc cs'`. But this is enough
for the totality checker, because our `SuffixAcc` proof is
obviously getting strictly smaller with every iteration.

With the exception of some niceties around dealing with bounds
and pretty printing parsing errors, this whole library is
built upon the interaction between `Suffix` and `SuffixAcc`.

## `SuffixRes`: Reintroducing Bounds and Errors

The `Suffix` predicate comes with additional benefits: It is
represented as a mere natural number at runtime, and its `toNat`
conversion is the identity function, so we can use this proof
and pass it around almost for free. It also allows us to compute
the next position in an input string.

Module `Text.SuffixRes` provides a small library of utility functions
built around the concept of consuming and converting a strict prefix 
of a string. We can use this to drastically simplify our lexer
without suffering a penalty in performance.

```idris
tok4 : (cs : List Char) -> SuffixRes Char cs Token
tok4 ('(' :: xs) = Succ (TSym '(') xs
tok4 (')' :: xs) = Succ (TSym ')') xs
tok4 ('*' :: xs) = Succ (TOp M) xs
tok4 ('+' :: xs) = Succ (TOp P) xs
tok4 xs          = TLit <$> dec xs

export
toks4 : String -> Either (Bounded Err) (List $ Bounded Token)
toks4 = mapFst (map Reason) . singleLineDropSpaces tok4
```

There are several functions for running tokenizers in module
`Text.SuffixRes`. One of them is `singleLineDropSpaces`: Use
this, when there are no multiline tokens and tokens can be separated
by arbitrary amounts of whitespace. This function will take care
of generating the bounds of tokens for us. As can be seen above, this
is a very convenient way of writing a tokenizer.

## Conclusion and Next Steps

I this section, I showed the core principle when writing provably
total tokenizer, and how to do so pretty conveniently. I'm planning
to add some more complex examples at a later time, but first, we are
going to parse the whole thing into a syntax tree of type `Expr`.
We will have a go at this in the [next section](Parser.md).

<!-- vi: filetype=idris2:syntax=markdown
-->
