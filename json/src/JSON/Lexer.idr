module JSON.Lexer

import Derive.Prelude
import JSON.Value
import Text.Parse.Manual

%default total
%language ElabReflection

public export
data JSToken : Type where
  Symbol   : Char -> JSToken
  Lit      : JSON -> JSToken

%runElab derive "JSToken" [Show,Eq]

%inline
fromChar : Char -> JSToken
fromChar = Symbol

export
Interpolation JSToken where
  interpolate (Symbol c) = show c
  interpolate (Lit x)  = "'\{show x}'"

public export
data JSErr : Type where
  ExpectedString  : JSErr
  InvalidEscape   : JSErr

%runElab derive "JSErr" [Show,Eq]

export
Interpolation JSErr where
  interpolate ExpectedString  = "Expected string literal"
  interpolate InvalidEscape   = "Invalid escape sequence"

public export %tcinline
0 ParseErr : Type
ParseErr = ParseError JSToken JSErr

strLit : SnocList Char -> JSToken
strLit = Lit . JString . cast

str : SnocList Char -> AutoTok Char JSToken
str sc ('\\' :: c  :: xs) = case c of
  '"'  => str (sc :< '"') xs
  'n'  => str (sc :< '\n') xs
  'f'  => str (sc :< '\f') xs
  'b'  => str (sc :< '\b') xs
  'r'  => str (sc :< '\r') xs
  't'  => str (sc :< '\t') xs
  '\\' => str (sc :< '\\') xs
  '/'  => str (sc :< '/') xs
  'u'  => case xs of
    w :: x :: y :: z :: t' =>
      if isHexDigit w && isHexDigit x && isHexDigit y && isHexDigit z
        then
          let c := cast $ hexDigit w * 0x1000 +
                          hexDigit x * 0x100 +
                          hexDigit y * 0x10 +
                          hexDigit z
           in str (sc :< c) t'
        else invalidEscape p t'
    _    => invalidEscape p xs
  _    => invalidEscape p xs
str sc ('"'  :: xs) = Succ (strLit sc) xs
str sc (c    :: xs) =
  if isControl c then range (InvalidControl c) p xs
  else str (sc :< c) xs
str sc []           = eoiAt p

term : Tok True Char JSToken
term (x :: xs) = case x of
  ',' => Succ ',' xs
  '"' => str [<] xs
  ':' => Succ ':' xs
  '[' => Succ '[' xs
  ']' => Succ ']' xs
  '{' => Succ '{' xs
  '}' => Succ '}' xs
  'n' => case xs of
    'u' :: 'l' :: 'l' :: t => Succ (Lit JNull) t
    _                      => unknown Same
  't' => case xs of
    'r' :: 'u' :: 'e' :: t => Succ (Lit $ JBool True) t
    _                      => unknown Same
  'f' => case xs of
    'a' :: 'l' :: 's' :: 'e' :: t => Succ (Lit $ JBool False) t
    _                             => unknown Same
  d   => suffix (Lit . JNumber . cast . cast {to = String}) $
         number [<] (d :: xs)

term []        = eoiAt Same

go :
     SnocList (Bounded JSToken)
 -> (pos   : Position)
 -> (cs    : List Char)
 -> (0 acc : SuffixAcc cs)
 -> Either (Bounded ParseErr) (List (Bounded JSToken))
go sx pos ('\n' :: xs) (SA rec) = go sx (incLine pos) xs rec
go sx pos (x :: xs)    (SA rec) =
  if isSpace x
     then go sx (incCol pos) xs rec
     else case term (x::xs) of
       Succ t xs' @{prf} =>
         let pos2 := addCol (toNat prf) pos
             bt   := bounded t pos pos2
          in go (sx :< bt) pos2 xs' rec
       Fail start errEnd r => Left $ boundedErr pos start errEnd (Reason r)
go sx _ [] _ = Right (sx <>> [])

export
lexJSON : String -> Either (Bounded ParseErr) (List (Bounded JSToken))
lexJSON s = go [<] begin (unpack s) suffixAcc
