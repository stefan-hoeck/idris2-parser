module Text.Lex.Util

import Text.Lex.Core

--------------------------------------------------------------------------------
--          Rewrites
--------------------------------------------------------------------------------

export %inline
orFst : Recognise (b || Delay c) -> Recognise b
orFst f cs = mapPrf or1 $ f cs

export %inline
orSnd : Recognise (b || Delay c) -> Recognise c
orSnd f cs = mapPrf or2 $ f cs

--------------------------------------------------------------------------------
--          Single-Character Lexers
--------------------------------------------------------------------------------

||| Recognise a specific character.
||| /[`x`]/
export
is : (x : Char) -> Lexer
is x = pred (==x)

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

charsOnto : SnocList Char -> (f : Char -> Char) -> List Char -> Recognise False
charsOnto sc f (x :: xs) (y :: ys) =
  if x == f y then charsOnto (sc :< y) f xs ys ~?> cons1  else Stop
charsOnto sc f (x :: xs) [] = Stop
charsOnto sc f []        cs = Res sc cs Same

chars : (Char -> Char) -> List Char -> Lexer
chars f []        = stop
chars f (x :: xs) =
  \case (c :: cs) => if x == f c then charsOnto [<c] f xs cs ~~> cons1 else Stop
        []        => Stop

export
exact : String -> Lexer
exact = chars id . unpack

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

export
newline : Lexer
newline ('\r' :: '\n' :: t) = Res [<'\r','\n'] t %search
newline ('\n' :: t)         = Res [<'\n'] t %search
newline ('\r' :: t)         = Res [<'\r'] t %search
newline _                   = Stop

||| Reads characters until the next newline character is
||| encountered.
export
manyTillNewline : Recognise False
manyTillNewline = go [<]
  where
    go : SnocList Char -> Recognise False
    go sc ts@('\n' :: _) = Res sc ts Same
    go sc ts@('\r' :: _) = Res sc ts Same
    go sc    (h    :: t) = go (sc :< h) t ~?> cons1
    go sc []             = Res sc [] Same

export
lineComment : (pre : Lexer) -> Lexer
lineComment pre = pre <+> manyTillNewline

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
stringHelper : SnocList Char -> Recognise False
stringHelper sc ('"' :: xs)         = Res (sc :< '"') xs %search
stringHelper sc ('\\' :: '"' :: xs) =
  stringHelper (sc :< '\\' :< '"') xs ~?> cons1 ~?> cons1
stringHelper sc (x :: xs)           = stringHelper (sc :< x) xs ~?> cons1
stringHelper sc []                  = Stop

export
stringLit : Lexer
stringLit ('"' :: cs) = stringHelper [<'"'] cs ~> cons1
stringLit _           = Stop
