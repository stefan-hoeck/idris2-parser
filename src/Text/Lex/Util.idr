module Text.Lex.Util

import Text.Lex.Core

public export %inline
pack : SnocList Char -> String
pack = pack . (<>> [])

||| Returns true if the character is a whitespace character.
|||
||| This a better-performing alternative to `isSpace` from the Prelude.
public export
isWhitespace : Char -> Bool
isWhitespace ' '    = True
isWhitespace '\t'   = True
isWhitespace '\n'   = True
isWhitespace '\r'   = True
isWhitespace '\f'   = True
isWhitespace '\v'   = True
isWhitespace '\xa0' = True
isWhitespace _      = False

--------------------------------------------------------------------------------
--          Shifters
--------------------------------------------------------------------------------

namespace Shifter
  public export %inline
  digits : Shifter True Char
  digits = takeWhile1 isDigit

  public export
  intLit : Shifter True Char
  intLit sc ('-' :: t) = digits (sc :< '-') t ~> sh1
  intLit sc xs         = digits sc xs

  public export
  intLitPlus : Shifter True Char
  intLitPlus sc ('+' :: t) = digits (sc :< '+') t ~> sh1
  intLitPlus sc xs         = intLit sc xs

  export
  exactPrefix : Eq t => List t -> Shifter True t
  exactPrefix (f :: []) sc (h :: t) =
    if f == h then Res (sc :< h) t %search else Stop
  exactPrefix (f :: fs) sc (h :: t) =
    if f == h then exactPrefix fs (sc :< h) t ~> sh1 else Stop
  exactPrefix _ _ _ = Stop

--------------------------------------------------------------------------------
--          Single-Character Lexers
--------------------------------------------------------------------------------

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
space = pred isWhitespace

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
exact s = let cs := unpack s in Lift $ exactPrefix cs

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

||| Recognise a single whitespace character.
export
spaces : Lexer
spaces = preds isWhitespace

||| Recognise a single newline character sequence
export
newline : Lexer
newline = Lift $ \sc,cs => case cs of
  '\r' :: '\n' :: t => Res (sc :< '\r' :< '\n') t %search
  '\n' ::         t => Res (sc :< '\n') t %search
  '\r' ::         t => Res (sc :< '\r') t %search
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

--------------------------------------------------------------------------------
--          Literals
--------------------------------------------------------------------------------

export
stringShifter : Shifter False Char
stringShifter sc ('"'       :: xs) = Res (sc :< '"') xs %search
stringShifter sc ('\\' :: x :: xs) = stringShifter (sc :< '\\' :< x) xs ~?> sh2
stringShifter sc (x         :: xs) = stringShifter (sc :< x) xs ~?> sh1
stringShifter sc []                = Stop

export
stringLit : Lexer
stringLit = Lift $ \sc,cs => case cs of
  '"' :: t => stringShifter (sc :< '"') t ~> sh1
  _        => Stop

||| Recognise an integer literal (possibly with a '-' prefix)
||| /-?[0-9]+/
export %inline
intLit : Lexer
intLit = Lift intLit

||| Recognise an integer literal (possibly with a '+' or '-' prefix)
export %inline
intLitPlus : Lexer
intLitPlus = Lift intLitPlus
