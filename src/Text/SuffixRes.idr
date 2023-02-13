module Text.SuffixRes

import Text.Bounded
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

||| A tokenizing function, which will consume a strict
||| prefix of the input list or fail with a stop reason.
public export
0 Tok : (t,a : Type) -> Type
Tok t a = (ts : List t) -> SuffixRes t ts a

||| A tokenizing function, which will consume additional characters
||| from the input string. This can only be used if already some
||| have been consumed.
public export
0 AutoTok : (t,a : Type) -> Type
AutoTok t a =
     {orig     : List t}
  -> (xs       : List t)
  -> {auto   p : Suffix True xs orig}
  -> SuffixRes t orig a

||| A tokenizing function, which will consume additional characters
||| from the input string.
public export
0 OntoTok : (t,a : Type) -> Type
OntoTok t a =
     {orig     : List t}
  -> (xs       : List t)
  -> {auto   p : Suffix False xs orig}
  -> SuffixRes t orig a

public export %inline
tok : OntoTok t a -> Tok t a
tok f ts = f ts

public export %inline
autoTok : OntoTok t a -> AutoTok t a
autoTok f ts @{p} = f ts @{weaken p}

public export %inline
invalidEscape :
     {orig      : List t}
  -> {current   : List t}
  -> (suffixCur : Suffix b current orig)
  -> (0 rest    : List t)
  -> {auto sr   : Suffix False rest current}
  -> SuffixRes t orig a
invalidEscape sc rest = Stop (weaken sc) rest InvalidEscape

public export %inline
unknownRange :
     {orig      : List t}
  -> {current   : List t}
  -> (suffixCur : Suffix b current orig)
  -> (0 rest    : List t)
  -> {auto sr   : Suffix False rest current}
  -> SuffixRes t orig a
unknownRange sc rest = Stop (weaken sc) rest UnknownToken

public export %inline
whole :
     {orig      : List t}
  -> StopReason
  -> (0 current : List t)
  -> {auto suffixCur : Suffix False current orig}
  -> SuffixRes t orig a
whole r current = Stop Same current r

public export %inline
unknown :
     {orig      : List t}
  -> (0 current : List t)
  -> {auto suffixCur : Suffix False current orig}
  -> SuffixRes t orig a
unknown = whole UnknownToken

public export
failEOI :
     {0 current : List t}
  -> {orig      : List t}
  -> (suffixCur : Suffix b current orig)
  -> SuffixRes t orig a
failEOI sc = Stop {end = weaken sc} Same current EOI

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
dec : OntoTok Char Nat
dec (x::xs) = if isDigit x then dec1 (digit x) xs else unknown xs
dec []      = failEOI p

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
decSep : OntoTok Char Nat
decSep (x::xs) = if isDigit x then dec_1 (digit x) xs else unknown xs
decSep []      = failEOI p

||| Tries to read more binary digits onto a growing natural number.
public export
bin1 : (n : Nat) -> AutoTok Char Nat
bin1 n (x :: xs) = if isBinDigit x then bin1 (n*2 + binDigit x) xs else succ n p
bin1 n []        = succ n p

||| Tries to read a binary natural number.
||| Fails, if this does not contain at least one digit.
public export
bin : OntoTok Char Nat
bin (x::xs) = if isBinDigit x then bin1 (binDigit x) xs else unknown xs
bin []      = failEOI p

||| Tries to read more binary digits onto a growing natural number.
||| Supports underscores as separators for better readability.
public export
bin_1 : (n : Nat) -> AutoTok Char Nat
bin_1 n ('_' :: x :: xs) =
  if isBinDigit x then bin_1 (n*2 + binDigit x) xs else unknownRange p xs
bin_1 n (x :: xs) =
  if isBinDigit x then bin_1 (n*2 + binDigit x) xs else succ n p
bin_1 n []        = succ n p

||| Tries to read a binary natural number.
||| Fails, if this does not contain at least one digit.
||| Supports underscores as separators for better readability.
public export
binSep : OntoTok Char Nat
binSep (x::xs) = if isBinDigit x then bin_1 (binDigit x) xs else unknown xs
binSep []      = failEOI p

||| Tries to read more octal digits onto a growing natural number.
public export
oct1 : (n : Nat) -> AutoTok Char Nat
oct1 n (x :: xs) = if isOctDigit x then oct1 (n*2 + octDigit x) xs else succ n p
oct1 n []        = succ n p

||| Tries to read a octal natural number.
||| Fails, if this does not contain at least one digit.
public export
oct : OntoTok Char Nat
oct (x::xs) = if isOctDigit x then oct1 (octDigit x) xs else unknown xs
oct []      = failEOI p

||| Tries to read more octal digits onto a growing natural number.
||| Supports underscores as separators for better readability.
public export
oct_1 : (n : Nat) -> AutoTok Char Nat
oct_1 n ('_' :: x :: xs) =
  if isOctDigit x then oct_1 (n*2 + octDigit x) xs else unknownRange p xs
oct_1 n (x :: xs) =
  if isOctDigit x then oct_1 (n*2 + octDigit x) xs else succ n p
oct_1 n []        = succ n p

||| Tries to read a octal natural number.
||| Fails, if this does not contain at least one digit.
||| Supports underscores as separators for better readability.
public export
octSep : OntoTok Char Nat
octSep (x::xs) = if isOctDigit x then oct_1 (octDigit x) xs else unknown xs
octSep []      = failEOI p

||| Tries to read more hexadecimal digits onto a growing natural number.
public export
hex1 : (n : Nat) -> AutoTok Char Nat
hex1 n (x :: xs) = if isHexDigit x then hex1 (n*2 + hexDigit x) xs else succ n p
hex1 n []        = succ n p

||| Tries to read a hexadecimal natural number.
||| Fails, if this does not contain at least one digit.
public export
hex : OntoTok Char Nat
hex (x::xs) = if isHexDigit x then hex1 (hexDigit x) xs else unknown xs
hex []      = failEOI p

||| Tries to read more hexadecimal digits onto a growing natural number.
||| Supports underscores as separators for better readability.
public export
hex_1 : (n : Nat) -> AutoTok Char Nat
hex_1 n ('_' :: x :: xs) =
  if isHexDigit x then hex_1 (n*2 + hexDigit x) xs else unknownRange p xs
hex_1 n (x :: xs) =
  if isHexDigit x then hex_1 (n*2 + hexDigit x) xs else succ n p
hex_1 n []        = succ n p

||| Tries to read a hexadecimal natural number.
||| Fails, if this does not contain at least one digit.
||| Supports underscores as separators for better readability.
public export
hexSep : OntoTok Char Nat
hexSep (x::xs) = if isHexDigit x then hex_1 (hexDigit x) xs else unknown xs
hexSep []      = failEOI p

--------------------------------------------------------------------------------
--          Integer Literals
-----------------------------------------------------------------------------

||| A shifter that takes moves an integer prefix
public export
int : OntoTok Char Integer
int ('-' :: xs) = negate . cast <$> dec xs
int xs          = cast <$> dec xs

||| Like `int` but also allows an optional leading `'+'` character.
public export
intPlus : OntoTok Char Integer
intPlus ('+'::xs) = cast <$> dec xs
intPlus xs        = int xs

--------------------------------------------------------------------------------
--          Running Tokenizers
-----------------------------------------------------------------------------

||| Flag indicating whether whitespace characters should
||| be removed during lexing.
|||
||| This will only affect whitespace that is not consumed by
||| the tokenization function. Whitespace appearing within a
||| string literal, for instance, and being consumed by the
||| function converting the literal, will not be affected.
public export
data Spaces = Keep | Drop

||| Settings for repeatedly running a `Tok Char a` function.
|||
||| This describes mainly, how `Bound`s are generated (if at all).
|||
||| Use the `SingleLine` constructor, if all recognized tokens
||| are free of whitespace. This automatically means, that the
||| iterating function will not pass line breaks to the tokenizer.
|||
||| Use the `MultiLine` constructor, if tokens might have consumed
||| some line breaks (if you're grammar supports multi-line string,
||| for instance). This will require a second traversal of the
||| consumed characters to figure out the bounds of a lexeme, so
||| it might have an effect on performance. This will be mainly an
||| issue if you write high-performance lexers, however.
|||
||| Use the `NoBounds`, if you don't want to pair the generated
||| tokens with proper bounds. This will improve performance, but
||| it will make it harder (or even impossible), to get nicely positioned
||| error messages.
public export
data TokSettings : Type where
  SingleLine : TokSettings
  MultiLine  : TokSettings
  NoBounds   : TokSettings

public export
0 Eff : TokSettings -> Type -> Type
Eff SingleLine y = Bounded y
Eff MultiLine  y = Bounded y
Eff NoBounds   y = y

public export
runTok : Tok t a -> List t -> Either StopReason (List a)
runTok f cs = go [<] cs suffixAcc
  where
    go : SnocList a
      -> (ts : List t)
      -> (0 acc : SuffixAcc ts)
      -> Either StopReason (List a)
    go sx [] _      = Right $ sx <>> []
    go sx xs (SA r) = case f xs of
      Succ v xs2 => go (sx :< v) xs2 r
      Stop _ _ r => Left r

public export
noBoundsDropSpaces : Tok Char a -> String -> Either StopReason (List a)
noBoundsDropSpaces f s = go [<] (unpack s) suffixAcc
  where
    go : SnocList a
      -> (ts : List Char)
      -> (0 acc : SuffixAcc ts)
      -> Either StopReason (List a)
    go sx []       _     = Right $ sx <>> []
    go sx (c::cs) (SA r) =
      if isSpace c then go sx cs r
      else case f (c::cs) of
        Succ v xs2 => go (sx :< v) xs2 r
        Stop _ _ r => Left r

public export
singleLineDropSpaces :
     Tok Char a
  -> String
  -> Either (Bounded StopReason) (List $ Bounded a)
singleLineDropSpaces f s = go begin [<] (unpack s) suffixAcc
  where
    go : Position
      -> SnocList (Bounded a)
      -> (ts : List Char)
      -> (0 acc : SuffixAcc ts)
      -> Either (Bounded StopReason) (List $ Bounded a)
    go p1 sx []       _        = Right $ sx <>> []
    go p1 sx ('\n'::cs) (SA r) = go (incLine p1) sx cs r
    go p1 sx (c::cs)    (SA r) =
      if isSpace c then go (incCol p1) sx cs r
      else case f (c::cs) of
        Succ v xs2 @{p}     =>
          let p2 := move p1 p
           in go p2 (sx :< bounded v p1 p2) xs2 r
        Stop s e r => Left $ boundedErr p1 s e r

public export
multiLineDropSpaces :
     Tok Char a
  -> String
  -> Either (Bounded StopReason) (List $ Bounded a)
multiLineDropSpaces f s = go begin [<] (unpack s) suffixAcc
  where
    go : Position
      -> SnocList (Bounded a)
      -> (ts : List Char)
      -> (0 acc : SuffixAcc ts)
      -> Either (Bounded StopReason) (List $ Bounded a)
    go p1 sx []       _        = Right $ sx <>> []
    go p1 sx ('\n'::cs) (SA r) = go (incLine p1) sx cs r
    go p1 sx (c::cs)    (SA r) =
      if isSpace c then go (incCol p1) sx cs r
      else case f (c::cs) of
        Succ v xs2 @{p}     =>
          let p2 := endPos p1 p
           in go p2 (sx :< bounded v p1 p2) xs2 r
        Stop s e r => Left $ boundedErr p1 s e r

public export
multiline :
     Tok Char a
  -> String
  -> Either (Bounded StopReason) (List $ Bounded a)
multiline f s = go begin [<] (unpack s) suffixAcc
  where
    go : Position
      -> SnocList (Bounded a)
      -> (ts : List Char)
      -> (0 acc : SuffixAcc ts)
      -> Either (Bounded StopReason) (List $ Bounded a)
    go p1 sx [] _      = Right $ sx <>> []
    go p1 sx cs (SA r) = case f cs of
      Succ v xs2 @{p}     =>
        let p2 := endPos p1 p
         in go p2 (sx :< bounded v p1 p2) xs2 r
      Stop s e r => Left $ boundedErr p1 s e r

public export
singleline :
     Tok t a
  -> List t
  -> Either (Bounded StopReason) (List $ Bounded a)
singleline f s = go begin [<] s suffixAcc
  where
    go : Position
      -> SnocList (Bounded a)
      -> (ts : List t)
      -> (0 acc : SuffixAcc ts)
      -> Either (Bounded StopReason) (List $ Bounded a)
    go p1 sx [] _      = Right $ sx <>> []
    go p1 sx cs (SA r) = case f cs of
      Succ v xs2 @{p}     =>
        let p2 := move p1 p
         in go p2 (sx :< bounded v p1 p2) xs2 r
      Stop x _ y @{e} =>
        let p2 := move p1 x
            p3 := move p2 e
         in Left $ bounded y p2 p3
