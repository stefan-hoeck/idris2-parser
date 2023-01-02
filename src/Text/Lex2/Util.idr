module Text.Lex2.Util

import Text.Lex2.Core

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
--          Rewrites
--------------------------------------------------------------------------------

export %inline
orFst : Recognise (b || Delay c) -> Recognise b
orFst f sc cs = mapPrf or1 $ f sc cs

export %inline
orSnd : Recognise (b || Delay c) -> Recognise c
orSnd f sc cs = mapPrf or2 $ f sc cs

--------------------------------------------------------------------------------
--          Single-Character Lexers
--------------------------------------------------------------------------------

||| Recognise a specific character.
||| /[`x`]/
export
is : (x : Char) -> Lexer
is c sc (x :: xs) = case prim__eq_Char c x of
  0 => Stop
  _ => Res (sc :< x) xs cons1
is c sc [] = Stop

||| Recognise a single whitespace character.
export
space : Lexer
space = pred isWhitespace

||| Recognise a single digit.
export
digit : Lexer
digit = pred isDigit

||| Recognise anything but the given character.
||| /[\^`x`]/
export
isNot : (x : Char) -> Lexer
isNot x = pred (/=x)

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
export
oneOf : String -> Lexer
oneOf s = let cs := unpack s in pred (`elem` cs)

||| Recognise a character in a range. Also works in reverse!
||| /[`start`-`end`]/
export
range : (start : Char) -> (end : Char) -> Lexer
range start end =
  let s := min start end
      e := max start end
   in pred (\x => x >= s && x <= e)

--------------------------------------------------------------------------------
--          Multi-Character Lexers
--------------------------------------------------------------------------------

charsOnto : (f : Char -> Char) -> List Char -> Recognise False
charsOnto f (x :: xs) sc (y :: ys) =
  if x == f y then charsOnto f xs (sc :< y) ys ~?> cons1  else Stop
charsOnto f (x :: xs) _  [] = Stop
charsOnto f []        sc cs = Res sc cs Same

chars : (Char -> Char) -> List Char -> Lexer
chars f []        = stop
chars f (x :: xs) = \sc,cs => case cs of
  h :: t =>
    if x == f h
      then charsOnto f xs (sc :< h) t ~~> cons1
      else Stop
  []     => Stop

export %inline
exact : String -> Lexer
exact s = let cs := unpack s in chars id cs

export
approx : String -> Lexer
approx = chars toUpper . map toUpper . unpack

||| Recognise a non-empty sequence of digits.
export
digits : Lexer
digits = preds isDigit

||| Recognises a non-empty sequence of the given characters
export
someOf : String -> Lexer
someOf s = let cs := unpack s in preds (`elem` cs)

||| Recognise some characters in a range. Also works in reverse!
||| /[`start`-`end`]/
export
ranges : (start : Char) -> (end : Char) -> Lexer
ranges start end =
  let s := min start end
      e := max start end
   in preds (\x => x >= s && x <= e)

||| Recognise a single whitespace character.
export
spaces : Lexer
spaces = preds isWhitespace

export
newline : Lexer
newline sc ('\r' :: '\n' :: t) = Res (sc :< '\r' :< '\n') t %search
newline sc ('\n' :: t)         = Res (sc :< '\n') t %search
newline sc ('\r' :: t)         = Res (sc :< '\r') t %search
newline _  _                   = Stop

||| Reads characters until the next newline character is
||| encountered.
export
manyTillNewline : Recognise False
manyTillNewline = preds0 $ \case {'\n' => False; '\r' => False; _ => True}

||| Reads characters until the next linefeed character (`'\n'`) is
||| encountered.
export
manyTillLineFeed : Recognise False
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
atLeast : (n : Nat) -> Lexer -> Recognise (isSucc n)
atLeast 0     f = many f
atLeast (S k) f = f <+> atLeast k f

export
manyUntil : (stopBefore : Recognise c) -> Lexer -> Recognise False
manyUntil sb l = many (reject sb <+> l)

export
someUntil : (stopBefore : Recognise c) -> Lexer -> Lexer
someUntil sb l = some (reject sb <+> l)

export
manyThen : (stopAfter : Recognise c) -> (l : Lexer) -> Recognise c
manyThen stopAfter l = manyUntil stopAfter l <+> stopAfter

--------------------------------------------------------------------------------
--          Literals
--------------------------------------------------------------------------------

export
stringHelper : Recognise False
stringHelper sc ('"' :: xs)         = Res (sc :< '"') xs %search
stringHelper sc ('\\' :: '"' :: xs) =
  stringHelper (sc :< '\\' :< '"') xs ~?> cons1 ~?> cons1
stringHelper sc (x :: xs)           = stringHelper (sc :< x) xs ~?> cons1
stringHelper sc []                  = Stop

export
stringLit : Lexer
stringLit sc ('"' :: cs) = stringHelper (sc :< '"') cs ~> cons1
stringLit _  _           = Stop

||| Recognise an integer literal (possibly with a '-' prefix)
||| /-?[0-9]+/
export
intLit : Lexer
intLit sc ('-' :: cs) = digits (sc :< '-') cs ~> cons1
intLit sc cs          = digits sc cs
