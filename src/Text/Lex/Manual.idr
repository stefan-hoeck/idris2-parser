module Text.Lex.Manual

import Data.List.Quantifiers
import Text.Bounds
import public Text.ParseError
import public Data.List.Suffix
import public Data.List.Suffix.Result

%default total

||| Result of running a (strict) tokenizer.
public export
0 LexRes : (b : Bool) -> List Char -> (e,a : Type) -> Type
LexRes b ts e a = Result b Char ts (ParseError Void e) a

--------------------------------------------------------------------------------
--          Combinators
--------------------------------------------------------------------------------

public export
(<|>) :
     Result b t ts r a
  -> Lazy (Result b t ts r a)
  -> Result b t ts r a
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
0 Tok : (b : Bool) -> (e,a : Type) -> Type
Tok b e a = (cs : List Char) -> LexRes b cs e a

||| A tokenizing function, which will consume additional characters
||| from the input string. This can only be used if already some
||| have been consumed.
public export
0 AutoTok : (e,a : Type) -> Type
AutoTok e a =
     {orig     : List Char}
  -> (cs       : List Char)
  -> {auto   p : Suffix True cs orig}
  -> LexRes True orig e a

||| A tokenizing function that cannot fail.
public export
0 SafeTok : (a : Type) -> Type
SafeTok a =
     {0 e      : Type}
  -> {orig     : List Char}
  -> (cs       : List Char)
  -> {auto   p : Suffix True cs orig}
  -> LexRes True orig e a

||| A tokenizing function, which will consume additional characters
||| from the input string.
public export
0 StrictTok : (e,a : Type) -> Type
StrictTok e a =
     {orig     : List Char}
  -> (cs       : List Char)
  -> {auto   p : Suffix False cs orig}
  -> LexRes True orig e a

public export %inline
tok : StrictTok e a -> Tok True e a
tok f ts = f ts

public export %inline
autoTok : StrictTok e a -> AutoTok e a
autoTok f ts @{p} = weakens $ f ts @{weaken p}

public export %inline
safeTok : SafeTok a -> AutoTok e a
safeTok f ts = f ts

public export %inline
range :
     {0 b, bres : Bool}
  -> {orig      : List Char}
  -> {errBegin  : List Char}
  -> (err       : ParseError Void e)
  -> (suffixCur : Suffix b errBegin orig)
  -> (0 errEnd  : List Char)
  -> {auto sr   : Suffix False errEnd errBegin}
  -> LexRes bres orig e a
range err sc errEnd = Fail (weaken sc) errEnd err

public export %inline
invalidEscape :
     {0 b, bres : Bool}
  -> {orig      : List Char}
  -> {errBegin  : List Char}
  -> (suffixCur : Suffix b errBegin orig)
  -> (0 errEnd  : List Char)
  -> {auto sr   : Suffix False errEnd errBegin}
  -> LexRes bres orig e a
invalidEscape = range InvalidEscape

public export %inline
unknownRange :
     {0 b, bres : Bool}
  -> {orig      : List Char}
  -> {errBegin  : List Char}
  -> (suffixCur : Suffix b errBegin orig)
  -> (0 errEnd  : List Char)
  -> {auto sr   : Suffix False errEnd errBegin}
  -> LexRes bres orig e a
unknownRange sc ee = range (Unknown . Left $ packPrefix sr) sc ee

public export %inline
single :
     {0 bres        : Bool}
  -> {c             : Char}
  -> {orig,errEnd   : List Char}
  -> (err           : ParseError Void e)
  -> (suffixCur     : Suffix b (c::errEnd) orig)
  -> LexRes bres orig e a
single r p = range r p errEnd

public export %inline
unknown :
     {0 bres        : Bool}
  -> {c             : Char}
  -> {orig,errEnd   : List Char}
  -> (suffixCur     : Suffix b (c::errEnd) orig)
  -> LexRes bres orig e a
unknown sc = unknownRange sc errEnd

public export %inline
eoiAt :
     {0 b, bres  : Bool}
  -> {orig       : List Char}
  -> (suffixCur  : Suffix b [] orig)
  -> LexRes bres orig e a
eoiAt sc = range EOI sc []

public export %inline
failCharClass :
     {0 bres        : Bool}
  -> {c             : Char}
  -> {orig,errEnd   : List Char}
  -> (class         : CharClass)
  -> (suffixCur     : Suffix b (c::errEnd) orig)
  -> LexRes bres orig e a
failCharClass cc = single (ExpectedChar cc)

public export %inline
failDigit :
     {0 bres        : Bool}
  -> {c             : Char}
  -> {orig,errEnd   : List Char}
  -> (tpe           : DigitType)
  -> (suffixCur     : Suffix b (c::errEnd) orig)
  -> LexRes bres orig e a
failDigit = failCharClass . Digit

public export %inline
fail :
     {0 b, bres : Bool}
  -> {errBegin  : List Char}
  -> {orig      : List Char}
  -> (suffixCur : Suffix b errBegin orig)
  -> LexRes bres orig e a
fail {errBegin = x::xs} p = unknown p
fail {errBegin = []}    p = eoiAt p

--------------------------------------------------------------------------------
--          Natural Numbers
--------------------------------------------------------------------------------

||| Tries to read additional decimal digits onto a growing natural number.
public export
dec1 : (n : Nat) -> SafeTok Nat
dec1 n (x::xs) = if isDigit x then dec1 (n*10 + digit x) xs else succ n p
dec1 n []      = succ n p

||| Tries to read a natural number. Fails, if this does not contain at least
||| one digit.
public export
dec : StrictTok e Nat
dec (x::xs) = if isDigit x then dec1 (digit x) xs else failDigit Dec p
dec []      = eoiAt p

||| Tries to read more decimal digits onto a growing natural number.
||| Supports underscores as separators for better readability.
public export
dec_1 : (n : Nat) -> AutoTok e Nat
dec_1 n ('_'::x::xs) =
  if isDigit x then dec_1 (n*10 + digit x) xs else failDigit Dec (uncons p)
dec_1 n (x::xs)      = if isDigit x then dec_1 (n*10 + digit x) xs else succ n p
dec_1 n []           = Succ n []

||| Tries to read a natural number.
||| Supports underscores as separators for better readability.
public export
decSep : StrictTok e Nat
decSep (x::xs) = if isDigit x then dec_1 (digit x) xs else failDigit Dec p
decSep []      = eoiAt p

||| Tries to read more binary digits onto a growing natural number.
public export
bin1 : (n : Nat) -> SafeTok Nat
bin1 n (x :: xs) = if isBinDigit x then bin1 (n*2 + binDigit x) xs else succ n p
bin1 n []        = succ n p

||| Tries to read a binary natural number.
||| Fails, if this does not contain at least one digit.
public export
bin : StrictTok e Nat
bin (x::xs) = if isBinDigit x then bin1 (binDigit x) xs else failDigit Bin p
bin []      = eoiAt p

||| Tries to read more binary digits onto a growing natural number.
||| Supports underscores as separators for better readability.
public export
bin_1 : (n : Nat) -> AutoTok e Nat
bin_1 n ('_' :: x :: xs) =
  if isBinDigit x then bin_1 (n*2 + binDigit x) xs else failDigit Bin (uncons p)
bin_1 n (x :: xs) =
  if isBinDigit x then bin_1 (n*2 + binDigit x) xs else succ n p
bin_1 n []        = succ n p

||| Tries to read a binary natural number.
||| Fails, if this does not contain at least one digit.
||| Supports underscores as separators for better readability.
public export
binSep : StrictTok e Nat
binSep (x::xs) = if isBinDigit x then bin_1 (binDigit x) xs else failDigit Bin p
binSep []      = eoiAt p

||| Tries to read more octal digits onto a growing natural number.
public export
oct1 : (n : Nat) -> SafeTok Nat
oct1 n (x :: xs) = if isOctDigit x then oct1 (n*8 + octDigit x) xs else succ n p
oct1 n []        = succ n p

||| Tries to read a octal natural number.
||| Fails, if this does not contain at least one digit.
public export
oct : StrictTok e Nat
oct (x::xs) = if isOctDigit x then oct1 (octDigit x) xs else failDigit Oct p
oct []      = eoiAt p

||| Tries to read more octal digits onto a growing natural number.
||| Supports underscores as separators for better readability.
public export
oct_1 : (n : Nat) -> AutoTok e Nat
oct_1 n ('_' :: x :: xs) =
  if isOctDigit x then oct_1 (n*8 + octDigit x) xs else failDigit Oct (uncons p)
oct_1 n (x :: xs) =
  if isOctDigit x then oct_1 (n*8 + octDigit x) xs else succ n p
oct_1 n []        = succ n p

||| Tries to read a octal natural number.
||| Fails, if this does not contain at least one digit.
||| Supports underscores as separators for better readability.
public export
octSep : StrictTok e Nat
octSep (x::xs) = if isOctDigit x then oct_1 (octDigit x) xs else failDigit Oct p
octSep []      = eoiAt p

||| Tries to read more hexadecimal digits onto a growing natural number.
public export
hex1 : (n : Nat) -> SafeTok Nat
hex1 n (x :: xs) = if isHexDigit x then hex1 (n*16 + hexDigit x) xs else succ n p
hex1 n []        = succ n p

||| Tries to read a hexadecimal natural number.
||| Fails, if this does not contain at least one digit.
public export
hex : StrictTok e Nat
hex (x::xs) = if isHexDigit x then hex1 (hexDigit x) xs else failDigit Hex p
hex []      = eoiAt p

||| Tries to read more hexadecimal digits onto a growing natural number.
||| Supports underscores as separators for better readability.
public export
hex_1 : (n : Nat) -> AutoTok e Nat
hex_1 n ('_' :: x :: xs) =
  if isHexDigit x then hex_1 (n*16 + hexDigit x) xs else failDigit Hex (uncons p)
hex_1 n (x :: xs) =
  if isHexDigit x then hex_1 (n*16 + hexDigit x) xs else succ n p
hex_1 n []        = succ n p

||| Tries to read a hexadecimal natural number.
||| Fails, if this does not contain at least one digit.
||| Supports underscores as separators for better readability.
public export
hexSep : StrictTok e Nat
hexSep (x::xs) = if isHexDigit x then hex_1 (hexDigit x) xs else failDigit Hex p
hexSep []      = eoiAt p

--------------------------------------------------------------------------------
--          Integer Literals
-----------------------------------------------------------------------------

||| A shifter that takes moves an integer prefix
public export
int : StrictTok e Integer
int ('-' :: xs) = negate . cast <$> dec xs
int xs          = cast <$> dec xs

||| Like `int` but also allows an optional leading `'+'` character.
public export
intPlus : StrictTok e Integer
intPlus ('+'::xs) = cast <$> dec xs
intPlus xs        = int xs

--------------------------------------------------------------------------------
--          Other Convertions
-----------------------------------------------------------------------------

public export
takeJustOnto : SnocList y -> (Char -> Maybe y) -> SafeTok (SnocList y)
takeJustOnto sx f (x :: xs) = case f x of
  Just vb => takeJustOnto (sx :< vb) f xs
  Nothing => Succ sx (x::xs)
takeJustOnto sx f []        = Succ sx []

||| Consumes and converts a list prefix until the given
||| function returns `Nothing`.
public export %inline
takeJust : (Char -> Maybe y) -> SafeTok (SnocList y)
takeJust f = takeJustOnto [<] f

||| Consumes and converts a strict list prefix until the given
||| function returns `Nothing`.
public export %inline
takeJust1 : (Char -> Maybe y) -> StrictTok e (SnocList y)
takeJust1 f (x::xs) = case f x of
  Just vb => takeJustOnto [<vb] f xs
  Nothing => unknown p
takeJust1 _ [] = eoiAt p

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
     Tok True e a
  -> String
  -> Either (Bounded $ ParseError Void e) (List $ Bounded a)
singleLineDropSpaces f s = go begin [<] (unpack s) suffixAcc
  where
    go : Position
      -> SnocList (Bounded a)
      -> (ts : List Char)
      -> (0 acc : SuffixAcc ts)
      -> Either (Bounded $ ParseError Void e) (List $ Bounded a)
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
     Tok True e a
  -> String
  -> Either (Bounded $ ParseError Void e) (List $ Bounded a)
multiLineDropSpaces f s = go begin [<] (unpack s) suffixAcc
  where
    go : Position
      -> SnocList (Bounded a)
      -> (ts : List Char)
      -> (0 acc : SuffixAcc ts)
      -> Either (Bounded $ ParseError Void e) (List $ Bounded a)
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
     Tok True e a
  -> String
  -> Either (Bounded $ ParseError Void e) (List $ Bounded a)
lexManual f s = go begin [<] (unpack s) suffixAcc
  where
    go : Position
      -> SnocList (Bounded a)
      -> (ts : List Char)
      -> (0 acc : SuffixAcc ts)
      -> Either (Bounded $ ParseError Void e) (List $ Bounded a)
    go p1 sx [] _      = Right $ sx <>> []
    go p1 sx cs (SA r) = case f cs of
      Succ v xs2 @{p}     =>
        let p2 := endPos p1 p
         in go p2 (sx :< bounded v p1 p2) xs2 r
      Fail s e r => Left $ boundedErr p1 s e r
