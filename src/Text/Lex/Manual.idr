module Text.Lex.Manual

import Text.Bounds
import public Text.ParseError
import public Data.List.Suffix
import public Data.List.Suffix.Result

%default total

||| Result of running a (strict) tokenizer.
public export
0 SuffixRes : (t : Type) -> List t -> (a : Type) -> Type
SuffixRes t ts a = Result True t ts StopReason a

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
range :
     {orig      : List t}
  -> {current   : List t}
  -> StopReason
  -> (suffixCur : Suffix b current orig)
  -> (0 rest    : List t)
  -> {auto sr   : Suffix False rest current}
  -> SuffixRes t orig a
range r sc rest = Fail (weaken sc) rest r

public export %inline
invalidEscape :
     {orig      : List t}
  -> {current   : List t}
  -> (suffixCur : Suffix b current orig)
  -> (0 rest    : List t)
  -> {auto sr   : Suffix False rest current}
  -> SuffixRes t orig a
invalidEscape = range InvalidEscape

public export %inline
unknownRange :
     {orig      : List t}
  -> {current   : List t}
  -> (suffixCur : Suffix b current orig)
  -> (0 rest    : List t)
  -> {auto sr   : Suffix False rest current}
  -> SuffixRes t orig a
unknownRange = range UnknownToken

public export %inline
whole :
     {orig      : List t}
  -> StopReason
  -> (0 current : List t)
  -> {auto suffixCur : Suffix False current orig}
  -> SuffixRes t orig a
whole r current = Fail Same current r

public export %inline
unknown :
     {orig      : List t}
  -> (0 current : List t)
  -> {auto suffixCur : Suffix False current orig}
  -> SuffixRes t orig a
unknown = whole UnknownToken

public export %inline
failEOI :
     {0 current : List t}
  -> {orig      : List t}
  -> (suffixCur : Suffix b current orig)
  -> SuffixRes t orig a
failEOI sc = Fail {end = weaken sc} Same current EOI

public export %inline
failEmpty : SuffixRes t [] a
failEmpty = Fail Same [] EOI

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
oct1 n (x :: xs) = if isOctDigit x then oct1 (n*8 + octDigit x) xs else succ n p
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
  if isOctDigit x then oct_1 (n*8 + octDigit x) xs else unknownRange p xs
oct_1 n (x :: xs) =
  if isOctDigit x then oct_1 (n*8 + octDigit x) xs else succ n p
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
hex1 n (x :: xs) = if isHexDigit x then hex1 (n*16 + hexDigit x) xs else succ n p
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
  if isHexDigit x then hex_1 (n*16 + hexDigit x) xs else unknownRange p xs
hex_1 n (x :: xs) =
  if isHexDigit x then hex_1 (n*16 + hexDigit x) xs else succ n p
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

||| Repeatedly consumes a strict prefix of a list of characters
||| until the whole list is consumed. Drops all white space
||| it encounters (unsing `Prelude.isSpace` to determine, what is
||| a whitespace character).
|||
||| This assumes that every token is on a single line. Therefore, it is
||| more efficient than `multilineDropSpaces`, because it does not have
||| to traverse the consumed characters to find line breaks.
|||
||| This is provably total, due to the strictness of the consuming
||| function.
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
        Fail s e r => Left $ boundedErr p1 s e r

||| Like `singleLineDropSpaces`, but consumed tokens might be
||| spread across several lines.
|||
||| This is provably total, due to the strictness of the consuming
||| function.
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
        Fail s e r => Left $ boundedErr p1 s e r

||| Repeatedly consumes a strict prefix of a list of characters
||| until the whole list is consumed. It uses the amount of characters
||| consumed to determine the bounds of the consumed lexemes.
|||
||| This is provably total, due to the strictness of the consuming
||| function.
public export
lexManual :
     Tok Char a
  -> String
  -> Either (Bounded StopReason) (List $ Bounded a)
lexManual f s = go begin [<] (unpack s) suffixAcc
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
      Fail s e r => Left $ boundedErr p1 s e r
