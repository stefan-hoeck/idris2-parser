module Text.Lex.SuffixRes

import public Data.List.Suffix

%default total

--------------------------------------------------------------------------------
--         Lexing
--------------------------------------------------------------------------------

||| Result of consuming and converting a (possibly strict) prefix
||| of a list of tokens.
|||
||| This comes with a non-erased proof about the number of tokens
||| consumed, which can be used to calculate the bounds of a lexeme.
|||
||| Use this for writing simple, high-performance tokenizers, which
||| (in the case of strict results) are guaranteed to terminate. This module
||| provides some utilities for consuming and converting prefixes
||| of tokens, but for a nicer interface, consider using `Text.Lex.Tokenizer`
||| (at the cost of a drop in performance).
|||
||| @ strict : True if a strict prefix of the list of tokens has
|||            been consumed.
||| @ t      : the type of token consumed.
||| @ ts     : the original list of tokens
||| @ a      : the result type
public export
data SuffixRes :
     (strict : Bool)
  -> (t : Type)
  -> List t
  -> (a : Type)
  -> Type where

  Succ :
       {0 t,a : Type}
    -> {0 ts : List t}
    -> (val : a)
    -> (xs : List t)
    -> {auto p : Suffix b xs ts}
    -> SuffixRes b t ts a

  Fail : SuffixRes b t ts a

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export
swapOr : {0 x,y : _} -> SuffixRes (x || y) t ts a -> SuffixRes (y || x) t ts a
swapOr = swapOr (\k => SuffixRes k t ts a)

public export %inline
orSame : {0 x : _} -> SuffixRes (x || x) t ts a -> SuffixRes x t ts a
orSame = orSame (\k => SuffixRes k t ts a)

public export %inline
orTrue : {0 x : _} -> SuffixRes (x || True) t ts a -> SuffixRes True t ts a
orTrue = orTrue (\k => SuffixRes k t ts a)

public export %inline
orFalse : {0 x : _} -> SuffixRes (x || False) t ts a -> SuffixRes x t ts a
orFalse = orFalse (\k => SuffixRes k t ts a)

public export %inline
swapAnd : {0 x,y : _} -> SuffixRes (x && y) t ts a -> SuffixRes (y && x) t ts a
swapAnd = swapAnd (\k => SuffixRes k t ts a)

public export %inline
andSame : {0 x : _} -> SuffixRes (x && x) t ts a -> SuffixRes x t ts a
andSame = andSame (\k => SuffixRes k t ts a)

public export %inline
andTrue : {0 x : _} -> SuffixRes (x && True) t ts a -> SuffixRes x t ts a
andTrue = andTrue (\k => SuffixRes k t ts a)

public export %inline
andFalse : {0 x : _} -> SuffixRes (x && False) t ts a -> SuffixRes False t ts a
andFalse = andFalse (\k => SuffixRes k t ts a)

public export %inline
weaken : {0 x : _} -> SuffixRes x t ts a -> SuffixRes False t ts a
weaken (Succ val xs @{p}) = Succ val xs @{weaken p}
weaken Fail = Fail

public export %inline
weakens : {0 x : _} -> SuffixRes True t ts a -> SuffixRes x t ts a
weakens (Succ val xs @{p}) = Succ val xs @{weakens p}
weakens Fail = Fail

public export %inline
and1 : {0 x : _} -> SuffixRes x t ts a -> SuffixRes (x && y) t ts a
and1 (Succ val xs @{p}) = Succ val xs @{and1 p}
and1 Fail = Fail

public export %inline
and2 : {0 x : _} -> SuffixRes x t ts a -> SuffixRes (y && x) t ts a
and2 r = swapAnd $ and1 r

public export %inline
trans : SuffixRes b1 t xs a -> Suffix b2 xs ys -> SuffixRes (b1 || b2) t ys a
trans (Succ val ts @{p}) q = Succ val ts @{p ~> q}
trans Fail               _ = Fail

||| Operator alias for `trans`.
public export %inline
(~>) : SuffixRes b1 t xs a -> Suffix b2 xs ys -> SuffixRes (b1 || b2) t ys a
(~>) = trans

||| Flipped version of `(~>)`.
public export %inline
(<~) : Suffix b1 xs ys -> SuffixRes b2 t xs a -> SuffixRes (b1 || b2) t ys a
x <~ y = swapOr $ trans y x

||| Operator alias for `trans` where the result is always non-strict
public export %inline
(~?>) : SuffixRes b1 t xs a -> Suffix b2 xs ys -> SuffixRes False t ys a
(~?>) x y = weaken $ x ~> y

||| Operator alias for `trans` where the strictness of the first
||| `Suffix` dominates.
public export %inline
(~~>) : SuffixRes b1 t xs a -> Suffix True xs ys -> SuffixRes b1 t ys a
(~~>) x y = weakens $ y <~ x

||| Operator alias for `trans` where the strictness of the second
||| `Suffix` dominates.
public export %inline
(<~~) : Suffix b1 xs ys -> SuffixRes True t xs a -> SuffixRes b1 t ys a
(<~~) x y = weakens $ y ~> x

--------------------------------------------------------------------------------
--          Combinators
--------------------------------------------------------------------------------

public export
(<|>) :
     SuffixRes b1 t ts a
  -> Lazy (SuffixRes b2 t ts a)
  -> SuffixRes (b1 && b2) t ts a
Succ v xs @{p} <|> _  = Succ v xs @{and1 p}
Fail           <|> r2 = and2 r2

public export
Functor (SuffixRes b t ts) where
  map f (Succ v xs) = Succ (f v) xs
  map _ Fail        = Fail

--------------------------------------------------------------------------------
--         Character Utilities
--------------------------------------------------------------------------------

||| Returns true if the character is a space (`' '`) character.
public export %inline
isSpaceChar : Char -> Bool
isSpaceChar ' ' = True
isSpaceChar _   = False

||| Returns true if the character is a line feed (`'\n'`) character.
public export %inline
isLineFeed : Char -> Bool
isLineFeed '\n' = True
isLineFeed _    = False

public export %inline
Cast (SnocList Char) String where
  cast = pack . (<>> [])

||| Converts a character to an octal digit. This works under the
||| assumption that the character has already been verified to be
||| an octal digit.
public export
octDigit : Char -> Nat
octDigit '0' = 0
octDigit '1' = 1
octDigit '2' = 2
octDigit '3' = 3
octDigit '4' = 4
octDigit '5' = 5
octDigit '6' = 6
octDigit _   = 7

||| Converts a character to a decimal digit. This works under the
||| assumption that the character has already been verified to be
||| a decimal digit.
public export
digit : Char -> Nat
digit '8' = 8
digit '9' = 9
digit c   = octDigit c

||| Converts a character to a hexadecimal digit. This works under the
||| assumption that the character has already been verified to be
||| a hexadecimal digit.
public export
hexDigit : Char -> Nat
hexDigit c = case toLower c of
  'a' => 10
  'b' => 11
  'c' => 12
  'd' => 13
  'e' => 14
  'f' => 15
  c   => digit c

||| True if the given character is a binary digit.
public export
isBinDigit : Char -> Bool
isBinDigit '0' = True
isBinDigit '1' = True
isBinDigit _   = False

||| Converts a character to a binary digit. This works under the
||| assumption that the character has already been verified to be
||| a binary digit.
public export
binDigit : Char -> Nat
binDigit '0' = 0
binDigit _   = 1

--------------------------------------------------------------------------------
--          Tokenizers
--------------------------------------------------------------------------------

public export
0 Tok : Bool -> (t,a : Type) -> Type
Tok b t a = (xs : List t) -> SuffixRes b t xs a

public export
0 AutoTok : Bool -> (t,a : Type) -> Type
AutoTok s t a =
     {0 b      : Bool}
  -> {0 orig   : List t}
  -> (xs       : List t)
  -> {auto  su : Suffix b xs orig}
  -> SuffixRes (s || b) t orig a

public export
ontoDec : (n : Nat) -> AutoTok False Char Nat
ontoDec n (x :: xs) =
  if isDigit x then ontoDec (n*10 + digit x) xs else Succ n (x::xs)
ontoDec n []        = Succ n []

public export
nat : AutoTok True Char Nat
nat (x :: xs) = if isDigit x then ontoDec (digit x) xs else Fail
nat []        = Fail

public export
ontoBin : (n : Nat) -> AutoTok False Char Nat
ontoBin n (x :: xs) =
  if isBinDigit x then ontoBin (n*2 + binDigit x) xs else Succ n (x::xs)
ontoBin n []        = Succ n []

public export
binNat : AutoTok True Char Nat
binNat (x :: xs) = if isBinDigit x then ontoBin (binDigit x) xs else Fail
binNat _                       = Fail

public export
ontoOct : (n : Nat) -> AutoTok False Char Nat
ontoOct n (x :: xs) =
  if isOctDigit x then ontoOct (n*8 + octDigit x) xs else Succ n (x::xs)
ontoOct n []        = Succ n []

public export
octNat : AutoTok True Char Nat
octNat (x :: xs) = if isOctDigit x then ontoOct (octDigit x) xs else Fail
octNat _         = Fail

public export
ontoHex : (n : Nat) -> AutoTok False Char Nat
ontoHex n (x :: xs) =
  if isHexDigit x then ontoHex (n*16 + hexDigit x) xs else Succ n (x::xs)
ontoHex n []        = Succ n []

public export
hexNat : AutoTok True Char Nat
hexNat (x :: xs) = if isHexDigit x then ontoHex (hexDigit x) xs else Fail
hexNat _         = Fail

public export
int : AutoTok True Char Integer
int ('-' :: xs) = map (negate . cast) (nat {b} xs)
int xs          = map cast (nat {b} xs)

public export
intPlus : AutoTok True Char Integer
intPlus ('+' :: xs) = int {b} xs
intPlus xs          = int {b} xs
