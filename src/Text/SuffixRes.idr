module Text.SuffixRes

import public Text.ParseError
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
data SuffixRes : (t : Type) -> List t -> (a : Type) -> Type where
  Succ :
       {0 t,a : Type}
    -> {0 ts : List t}
    -> (val : a)
    -> (xs : List t)
    -> {auto p : Suffix True xs ts}
    -> SuffixRes t ts a

  Stop :
       {0 t,a : Type}
    -> {ts,errStart : List t}
    -> (start : Suffix False errStart ts)
    -> (0 errEnd : List t)
    -> {auto end : Suffix False errEnd errStart}
    -> StopReason
    -> SuffixRes t ts a

public export %inline
succ : 
       {0 t,a : Type}
    -> {0 ts : List t}
    -> (val : a)
    -> {xs : List t}
    -> Suffix True xs ts
    -> SuffixRes t ts a
succ val _ = Succ val xs

--------------------------------------------------------------------------------
--          Combinators
--------------------------------------------------------------------------------

public export
(<|>) :
     SuffixRes t ts a
  -> Lazy (SuffixRes t ts a)
  -> SuffixRes t ts a
s@(Succ {}) <|> _ = s
_           <|> r = r

public export
Functor (SuffixRes t ts) where
  map f (Succ v xs)    = Succ (f v) xs
  map _ (Stop st ee r) = Stop st ee r

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
0 Tok : (t,a : Type) -> Type
Tok t a = (ts : List t) -> SuffixRes t ts a

public export
0 AutoTok : (t,a : Type) -> Type
AutoTok t a =
     {orig     : List t}
  -> (xs       : List t)
  -> {auto   p : Suffix True xs orig}
  -> SuffixRes t orig a

public export %inline
invalidEscape :
     {orig      : List t}
  -> {current   : List t}
  -> (suffixCur : Suffix True current orig)
  -> (0 rest    : List t)
  -> {auto sr   : Suffix False rest current}
  -> SuffixRes t orig a
invalidEscape sc rest = Stop (weaken sc) rest InvalidEscape

public export %inline
unknownRange :
     {orig      : List t}
  -> {current   : List t}
  -> (suffixCur : Suffix True current orig)
  -> (0 rest    : List t)
  -> {auto sr   : Suffix False rest current}
  -> SuffixRes t orig a
unknownRange sc rest = Stop (weaken sc) rest UnknownToken

public export %inline
unknown :
     {orig      : List t}
  -> (0 current : List t)
  -> {auto suffixCur : Suffix False current orig}
  -> SuffixRes t orig a
unknown current = Stop Same current UnknownToken

public export
eoi :
     {0 current : List t}
  -> {orig      : List t}
  -> (suffixCur : Suffix True current orig)
  -> SuffixRes t orig a
eoi sc = Stop {end = weaken sc} Same current EOI

public export
failEmpty : SuffixRes t [] a
failEmpty = Stop Same [] EOI

--------------------------------------------------------------------------------
--          Natural Numbers
--------------------------------------------------------------------------------

||| Tries to read additional decimal digits onto a growing natural number.
public export
dec1 : (n : Nat) -> AutoTok Char Nat
dec1 n (x::xs) = if isDigit x then dec1 (n*10 + digit x) xs else succ n p
dec1 n []      = succ n p

||| Tries to read a natural number. Fails, if this does not contain at least
||| one digit.
public export
dec : AutoTok Char Nat
dec (x::xs) = if isDigit x then dec1 (digit x) xs else unknown xs
dec []      = eoi p

||| Tries to read more decimal digits onto a growing natural number.
||| Supports underscores as separators for better readability.
public export
dec_1 : (n : Nat) -> AutoTok Char Nat
dec_1 n ('_'::x::xs) =
  if isDigit x then dec_1 (n*10 + digit x) xs else unknownRange p xs
dec_1 n (x::xs)      = if isDigit x then dec_1 (n*10 + digit x) xs else succ n p
dec_1 n []           = Succ n []

||| Tries to read a natural number.
||| Supports underscores as separators for better readability.
public export
decSep : AutoTok Char Nat
decSep (x::xs) = if isDigit x then dec_1 (digit x) xs else unknown xs
decSep []      = eoi p

||| Tries to read more binary digits onto a growing natural number.
public export
ontoBin : (n : Nat) -> AutoTok Char Nat
ontoBin n (x :: xs) =
  if isBinDigit x then ontoBin (n*2 + binDigit x) xs else succ n p
ontoBin n []        = succ n p

||| Tries to read more binary digits onto a growing natural number.
||| Supports underscores as separators for better readability.
public export
ontoBinSep : (n : Nat) -> AutoTok Char Nat
ontoBinSep n ('_' :: x :: xs) =
  if isBinDigit x then ontoBinSep (n*2 + binDigit x) xs else unknownRange p xs
ontoBinSep n (x :: xs) =
  if isBinDigit x then ontoBinSep (n*2 + binDigit x) xs else succ n p
ontoBinSep n []        = succ n p

-- public export
-- binNat : Tok Char Nat
-- binNat ('0'::'b'::xs) = case xs of
--   h :: t => if isBinDigit h then ontoBin (binDigit h) t else unknownRange Same xs
--   []     => unknownRange Same []
-- binNat (h :: t) = Stop
-- 
-- public export
-- binNatSep : Tok Char Nat
-- binNatSep ('0' :: 'b' :: xs) = case xs of
--   h :: t => if isBinDigit h then ontoBinSep (binDigit h) t else Fail Same t
--   []     => Fail Same []
-- binNatSep _ = Stop
-- 
-- ||| Tries to read more octal digits onto a growing natural number.
-- public export
-- ontoOct : (n : Nat) -> AutoTok Char Nat
-- ontoOct n (x :: xs) =
--   if isOctDigit x then ontoOct (n*8 + octDigit x) xs else succ n p
-- ontoOct n []        = succ n p
-- 
-- ||| Tries to read more octal digits onto a growing natural number.
-- ||| Supports underscores as separators for better readability.
-- public export
-- ontoOctSep : (n : Nat) -> AutoTok Char Nat
-- ontoOctSep n ('_' :: x :: xs) =
--   if isOctDigit x then ontoOctSep (n*8 + octDigit x) xs else succ n p
-- ontoOctSep n (x :: xs) =
--   if isOctDigit x then ontoOctSep (n*8 + octDigit x) xs else succ n p
-- ontoOctSep n []        = succ n p
-- 
-- public export
-- octNat : Tok Char Nat
-- octNat ('0' :: 'o' :: xs) = case xs of
--   h :: t => if isOctDigit h then ontoOct (octDigit h) t else Fail ['0','o',h] t
--   []     => Fail ['0','o'] []
-- octNat _ = Stop
-- 
-- public export
-- octNatSep : Tok Char Nat
-- octNatSep ('0' :: 'o' :: xs) = case xs of
--   h :: t => if isOctDigit h then ontoOctSep (octDigit h) t else Fail ['0','o',h] t
--   []     => Fail ['0','o'] []
-- octNatSep _ = Stop
-- 
-- ||| Tries to read more hexadecimal digits onto a growing natural number.
-- public export
-- ontoHex : (n : Nat) -> AutoTok Char Nat
-- ontoHex n (x :: xs) =
--   if isHexDigit x then ontoHex (n*16 + hexDigit x) xs else succ n p
-- ontoHex n []        = succ n p
-- 
-- ||| Tries to read more octal digits onto a growing natural number.
-- ||| Supports underscores as separators for better readability.
-- public export
-- ontoHexSep : (n : Nat) -> AutoTok Char Nat
-- ontoHexSep n ('_' :: x :: xs) =
--   if isHexDigit x then ontoHexSep (n*16 + octDigit x) xs else succ n p
-- ontoHexSep n (x :: xs) =
--   if isHexDigit x then ontoHexSep (n*16 + octDigit x) xs else succ n p
-- ontoHexSep n []        = succ n p
-- 
-- public export
-- hexNat : Tok Char Nat
-- hexNat ('0' :: 'o' :: xs) = case xs of
--   h :: t => if isHexDigit h then ontoHex (hexDigit h) t else Fail ['0','o',h] t
--   []     => Fail ['0','o'] []
-- hexNat _ = Stop
-- 
-- public export
-- hexNatSep : Tok Char Nat
-- hexNatSep ('0' :: 'o' :: xs) = case xs of
--   h :: t => if isHexDigit h then ontoHexSep (hexDigit h) t else Fail ['0','o',h] t
--   []     => Fail ['0','o'] []
-- hexNatSep _ = Stop
-- 
--------------------------------------------------------------------------------
--          Floating Point Numbers
-----------------------------------------------------------------------------

||| A shifter that takes moves an integer prefix
public export
int : AutoTok Char Integer
int ('-' :: xs) = negate . cast <$> dec xs
int xs          = cast <$> dec xs

||| Like `int` but also allows an optional leading `'+'` character.
public export
intPlus : AutoTok Char Integer
intPlus ('+'::xs) = cast <$> dec xs
intPlus xs        = int xs
