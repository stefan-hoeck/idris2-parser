module Text.Lex.Util

import Text.Lex.Core
import Text.Lex.SuffixRes

--------------------------------------------------------------------------------
--          (Snoc)List Utilities
--------------------------------------------------------------------------------

public export
stripQuotes : SnocList Char -> String
stripQuotes (sx :< _) = case sx <>> [] of
  _ :: t => pack t
  _      => ""
stripQuotes [<]       = ""

namespace List
  export
  ltrim : List Char -> List Char
  ltrim (c :: cs) = if isSpace c then ltrim cs else (c :: cs)
  ltrim []        = []
  
  export
  countHashtag : List Char -> Nat
  countHashtag ('#' :: t) = S $ countHashtag t
  countHashtag _          = 0

namespace SnocList
  export
  rtrim : SnocList Char -> SnocList Char
  rtrim (sc :< c) = if isSpace c then rtrim sc else (sc :< c)
  rtrim [<]       = [<]

  export
  dropHead : Nat -> SnocList Char -> List Char
  dropHead n = drop n . (<>> [])
  
  export
  countHashtag : SnocList Char -> Nat
  countHashtag = countHashtag . (<>> [])

--------------------------------------------------------------------------------
--          Single-Character Lexers
--------------------------------------------------------------------------------

export
any : Recognise True t
any = autoLift tail

||| Recognise any character if the sub-lexer `l` fails.
||| /(?!`l`)./
export
non : (l : Lexer) -> Lexer
non l = reject l <+> any

||| Recognise a specific item.
||| /[`x`]/
export %inline
is : Eq t => (x : t) -> Recognise True t
is x = pred (==x)

||| Recognise anything but the given item.
||| /[\^`x`]/
export %inline
isNot : Eq t => (x : t) -> Recognise True t
isNot x = pred (/=x)

||| Recognise a single whitespace character.
export
space : Lexer
space = pred isSpace

||| Recognise a single digit.
export
digit : Lexer
digit = pred isDigit

||| Recognise a specific character (case-insensitive).
||| /[`x`]/i
export
like : (x : Char) -> Lexer
like x = let x' := toUpper x in pred ((x' ==) . toUpper)

||| Recognise anything but the given character (case-insensitive).
||| /[\^`x`]/i
export
notLike : (x : Char) -> Lexer
notLike x = let x' := toUpper x in pred ((x' /=) . toUpper)

||| Recognises one of the given characters.
export %inline
oneOf : Eq t => List t -> Recognise True t
oneOf ts = pred (`elem` ts)

||| Recognise a character in a range. Also works in reverse!
||| /[`start`-`end`]/
export %inline
range : Ord t => (start : t) -> (end : t) -> Recognise True t
range start end =
  let s := min start end
      e := max start end
   in pred (\x => x >= s && x <= e)

--------------------------------------------------------------------------------
--          Multi-Character Lexers
--------------------------------------------------------------------------------

export
prefixBy : (fs : List (t -> Bool)) -> Recognise True t
prefixBy (f :: []) = pred f
prefixBy (f :: fs) = pred f <+> prefixBy fs
prefixBy []        = stop

export
exact : String -> Lexer
exact s = let cs := unpack s in autoLift $ exact cs

export
approx : String -> Lexer
approx = prefixBy . map check . unpack
  where
    check : Char -> Char -> Bool
    check c d = toLower c == toLower d

||| Recognise a non-empty sequence of digits.
export
digits : Lexer
digits = preds isDigit

||| Recognise a single non-whitespace, non-alphanumeric character
||| /[\^\\sA-Za-z0-9]/
export
symbol : Lexer
symbol = pred (\x => not (isSpace x || isAlphaNum x))

||| Recognise one or more non-whitespace, non-alphanumeric characters
||| /[\^\\sA-Za-z0-9]+/
export
symbols : Lexer
symbols = some symbol

||| Recognise a single control character
||| /[\\x00-\\x1f\\x7f-\\x9f]/
export
control : Lexer
control = pred isControl

||| Recognise one or more control characters
||| /[\\x00-\\x1f\\x7f-\\x9f]+/
export
controls : Lexer
controls = some control

||| Recognises a non-empty sequence of the given items
export %inline
someOf : Eq t => List t -> Recognise True t
someOf ts = preds (`elem` ts)

||| Recognise some items in a range. Also works in reverse!
||| /[`start`-`end`]/
export %inline
ranges : Ord t => (start : t) -> (end : t) -> Recognise True t
ranges start end =
  let s := min start end
      e := max start end
   in preds (\x => x >= s && x <= e)

||| Recognise a non-empty sequence of whitespace characters.
export
spaces : Lexer
spaces = preds isSpace

||| Recognise a non-empty sequence of space characters.
export
spaceChars : Lexer
spaceChars = preds isSpaceChar

||| Recognise a single newline character sequence
export
newline : Lexer
newline = Lift $ \sc,cs => case cs of
  '\r' :: '\n' :: t => Succ t
  '\n' ::         t => Succ t
  '\r' ::         t => Succ t
  _                 => Stop

||| Reads characters until the next newline character is
||| encountered.
export
manyTillNewline : Recognise False Char
manyTillNewline = preds0 $ \case {'\n' => False; '\r' => False; _ => True}

||| Reads characters until the next linefeed character (`'\n'`) is
||| encountered.
export
manyTillLineFeed : Recognise False Char
manyTillLineFeed = preds0 $ \case {'\n' => False; _ => True}

||| Lexer for single line comments starting with the given prefix.
|||
||| This reads until (but does not include) the first newline
||| character `'\n'` or `'\r'`.
export
lineComment : (pre : Lexer) -> Lexer
lineComment pre = pre <+> manyTillNewline

||| Lexer for single line comments starting with the given prefix.
|||
||| This reads until (but does not include) the first line feed
||| character (`'\n'`).
export
linefeedComment : (pre : Lexer) -> Lexer
linefeedComment pre = pre <+> manyTillLineFeed

--------------------------------------------------------------------------------
--          Combinators
--------------------------------------------------------------------------------

export
atLeast : (n : Nat) -> Recognise True t -> Recognise (isSucc n) t
atLeast 0     f = many f
atLeast (S k) f = f <+> atLeast k f

export
manyUntil : (stopBefore : Recognise c t) -> Recognise True t -> Recognise False t
manyUntil sb l = many (reject sb <+> l)

export
someUntil : (stopBefore : Recognise c t) -> Recognise True t -> Recognise True t
someUntil sb l = some (reject sb <+> l)

export
manyThen : (stopAfter : Recognise c t) -> (l : Recognise True t) -> Recognise c t
manyThen stopAfter l = manyUntil stopAfter l <+> stopAfter

||| Recognise zero or more occurrences of a sub-lexer between
||| delimiting lexers
||| /`start`(`l`)\*?`end`/
export
surround : (start : Lexer) -> (end : Lexer) -> (l : Lexer) -> Lexer
surround start end l = start <+> manyThen end l

||| Recognise zero or more occurrences of a sub-lexer surrounded
||| by the same quote lexer on both sides (useful for strings)
||| /`q`(`l`)\*?`q`/
export
quote : (q : Lexer) -> (l : Lexer) -> Lexer
quote q l = surround q q l

||| Recognise an escape sub-lexer (often '\\') followed by
||| another sub-lexer
||| /[`esc`]`l`/
export
escape : (esc : Lexer) -> Lexer -> Lexer
escape esc l = esc <+> l

--------------------------------------------------------------------------------
--          Literals
--------------------------------------------------------------------------------

export
stringLit : Lexer
stringLit = autoLift string

||| Recognise an integer literal (possibly with a '-' prefix)
||| /-?[0-9]+/
export %inline
intLit : Lexer
intLit = autoLift int

||| Recognise an integer literal (possibly with a '+' or '-' prefix)
export %inline
intLitPlus : Lexer
intLitPlus = autoLift intPlus

export %inline
binDigits : Lexer
binDigits = preds isBinDigit

export %inline
hexDigits : Lexer
hexDigits = preds isHexDigit

export %inline
octDigits : Lexer
octDigits = preds isOctDigit

||| Recognise a binary literal, prefixed by "0b"
||| /0b[0-1]+/
export
binLit : Lexer
binLit = exact "0b" <+> binDigits

||| Recognise a hexidecimal literal, prefixed by "0x" or "0X"
||| /0[Xx][0-9A-Fa-f]+/
export
hexLit : Lexer
hexLit = approx "0x" <+> hexDigits

||| Recognise an octal literal, prefixed by "0o"
||| /0o[0-9A-Fa-f]+/
export
octLit : Lexer
octLit = exact "0o" <+> preds isOctDigit

||| Recognise a decimal integer literal with optional undescores for
||| improved readability.
export
digitsUnderscoredLit : Lexer
digitsUnderscoredLit = digits <+> many (is '_' <+> digits)

||| Recognise a binary literal with optional undescores for
||| improved readability.
export
binUnderscoredLit : Lexer
binUnderscoredLit = binLit <+> many (is '_' <+> binDigits)

||| Recognise a hexadecimal literal with optional undescores for
||| improved readability.
export
hexUnderscoredLit : Lexer
hexUnderscoredLit = hexLit <+> many (is '_' <+> hexDigits)

||| Recognise an octal literal with optional undescores for
||| improved readability.
export
octUnderscoredLit : Lexer
octUnderscoredLit = octLit <+> many (is '_' <+> octDigits)

||| Recognise a character literal, including escaped characters.
||| (Note: doesn't yet handle escape sequences such as \123)
||| /'(\\\\.|[\^'])'/
export
charLit : Lexer
charLit = let q = '\'' in
              is q <+> (escape (is '\\') (control <|> any) <|> isNot q) <+> is q
  where
    lexStr : List String -> Lexer
    lexStr [] = stop
    lexStr (t :: ts) = exact t <|> lexStr ts

    control : Lexer
    control = lexStr ["NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL",
                      "BS",  "HT",  "LF",  "VT",  "FF",  "CR",  "SO",  "SI",
                      "DLE", "DC1", "DC2", "DC3", "DC4", "NAK", "SYN", "ETB",
                      "CAN", "EM",  "SUB", "ESC", "FS",  "GS",  "RS",  "US",
                      "SP",  "DEL"]
                <|> (is 'x' <+> hexDigits)
                <|> (is 'o' <+> octDigits)
                <|> digits
