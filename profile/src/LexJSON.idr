module LexJSON

import JSON
import Derive.Prelude
import Text.Lex

%language ElabReflection
%default total

public export
data Tok : Type where
  BracketO : Tok
  BracketC : Tok
  BraceO   : Tok
  BraceC   : Tok
  Comma    : Tok
  Colon    : Tok
  Lit      : JSON -> Tok

%runElab derive "Tok" [Show,Eq]

str : SnocList Char -> AutoTok False Char Tok
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
          let c := cast $ fromHexDigit w * 0x1000 +
                          fromHexDigit x * 0x100 +
                          fromHexDigit y * 0x10 +
                          fromHexDigit z 
           in str (sc :< c) t'
        else Fail
    _    => Fail
  _    => Fail
str sc ('\\' :: []) = Fail
str sc ('"'  :: xs) = Succ (Lit $ JString $ pack sc) xs
str sc (c    :: xs) = str (sc :< c) xs
str sc []           = Fail

term : SuffixRes.Tok True Char Tok
term (x :: xs) = case x of
  ',' => Succ Comma xs
  '"' => str [<] xs
  ':' => Succ Colon xs
  '[' => Succ BracketO xs
  ']' => Succ BracketC xs
  '{' => Succ BraceO xs
  '}' => Succ BraceC xs
  'n' => case xs of
    'u' :: 'l' :: 'l' :: t => Succ (Lit JNull) t
    _                      => Fail
  't' => case xs of
    'r' :: 'u' :: 'e' :: t => Succ (Lit $ JBool True) t
    _                      => Fail
  'f' => case xs of
    'a' :: 'l' :: 's' :: 'e' :: t => Succ (Lit $ JBool False) t
    _                             => Fail
  d   => suffix (Lit . JNumber . cast . pack) $
         number {pre = [<]} (d :: xs) @{Same}
  
term []        = Fail

go :
     SnocList (Bounded Tok)
 -> (l,c   : Nat)
 -> (cs    : List Char)
 -> (0 acc : SuffixAcc cs)
 -> (SnocList (Bounded Tok),Nat,Nat,List Char)
go sx l c ('\n' :: xs) (SA rec) = go sx (l+1) 0 xs rec
go sx l c (x :: xs)    (SA rec) =
  if isSpace x
     then go sx l (c+1) xs rec
     else case term (x::xs) of
       Succ t xs' @{prf} =>
         let c2 := c + toNat prf
             bt := bounded t l c l c2
          in go (sx :< bt) l c2 xs' rec
       Fail              => (sx,l,c,x::xs)
go sx l c []           acc = (sx,l,c,[])

export
json : String -> (SnocList (Bounded Tok),Nat,Nat,List Char)
json s = go [<] 0 0 (unpack s) suffixAcc
