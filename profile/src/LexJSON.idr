module LexJSON

import JSON
import Derive.Prelude
import Text.Lex

%language ElabReflection
%default total

public export
data Paren = Bracket | Brace

%runElab derive "Paren" [Show,Eq,Ord]

public export
data Err : Type where
  Unclosed     : Paren -> Err
  Unexpected   : Paren -> Err
  Unrecognised : Err

%runElab derive "Err" [Show,Eq]

public export
data Tok : Type where
  TBracketO : Tok
  TBracketC : Tok
  TBraceO   : Tok
  TBraceC   : Tok
  TComma    : Tok
  TColon    : Tok
  TLit     : JSON -> Tok

%runElab derive "Tok" [Show,Eq]

str :
     SnocList Char
  -> (cs : List Char)
  -> {auto prf : Tail True cs cs'}
  -> DirectRes cs' Tok
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
str sc ('"'  :: xs) = Succ (TLit $ JString $ pack sc) xs
str sc (c    :: xs) = str (sc :< c) xs
str sc []           = Fail

toNum : DirectRes cs (SnocList Char) -> DirectRes cs Tok
toNum (Succ x ds) = Succ (TLit $ JNumber $ cast $ pack x) ds
toNum Fail        = Fail

digits,int,exp,dot,rest,digs :
     SnocList Char
  -> (cs : List Char)
  -> {auto prf : Tail True cs cs'}
  -> DirectRes cs' (SnocList Char)

num :
     SnocList Char
  -> (cs : List Char)
  -> {auto prf : Tail False cs cs'}
  -> DirectRes cs' (SnocList Char)

digits sc (x :: xs) = if isDigit x then digits (sc :< x) xs else Succ sc (x::xs)
digits sc []        = Succ sc []

int sc ('+' :: xs) = digits (sc :< '+') xs
int sc ('-' :: xs) = digits (sc :< '-') xs
int sc xs          = digits sc xs

exp sc ('e' :: xs) = int (sc :< 'e') xs
exp sc ('E' :: xs) = int (sc :< 'e') xs
exp sc xs          = Succ sc xs

dot sc (x :: xs) = if isDigit x then dot (sc :< x) xs else exp sc (x::xs)
dot sc []        = Succ sc []

rest sc ('.' :: x :: xs) = if isDigit x then dot (sc :< '.' :< x) xs else Fail
rest sc xs               = exp sc xs

digs sc (x :: xs) = if isDigit x then digs (sc :< x) xs else rest sc (x::xs)
digs sc []        = Succ sc []

num sc ('0' :: xs) = rest (sc :< '0') xs
num sc (x :: xs)   = if isDigit x then digs (sc :< x) xs else Fail
num sc []          = Fail

term : (cs : List Char) -> DirectRes cs Tok
term (x :: xs) = case x of
  ',' => Succ TComma xs
  '"' => str [<] xs
  ':' => Succ TColon xs
  '[' => Succ TBracketO xs
  ']' => Succ TBracketC xs
  '{' => Succ TBraceO xs
  '}' => Succ TBraceC xs
  'n' => case xs of
    'u' :: 'l' :: 'l' :: t => Succ (TLit JNull) t
    _                      => Fail
  't' => case xs of
    'r' :: 'u' :: 'e' :: t => Succ (TLit $ JBool True) t
    _                      => Fail
  'f' => case xs of
    'a' :: 'l' :: 's' :: 'e' :: t => Succ (TLit $ JBool False) t
    _                             => Fail
  '-' => toNum $ num [<'-'] xs
  d   => toNum $ num [<] (d :: xs)
  
term []        = Fail

go :
     SnocList (Bounded Tok)
 -> (l,c   : Nat)
 -> (cs    : List Char)
 -> (0 acc : SuffixAcc cs)
 -> (SnocList (Bounded Tok),Nat,Nat,List Char)
go sx l c ('\n' :: xs) (Access rec) = go sx (l+1) 0 xs (rec xs %search)
go sx l c (x :: xs)    (Access rec) =
  if isSpace x
     then go sx l (c+1) xs (rec xs %search)
     else case term (x::xs) of
       Succ t xs' @{prf} =>
         let c2 := c + tailToNat prf
             bt := bounded t l c l c2
          in go (sx :< bt) l c2 xs' (rec xs' $ suffix prf)
       Fail              => (sx,l,c,x::xs)
go sx l c []           acc = (sx,l,c,[])

export
json : String -> (SnocList (Bounded Tok),Nat,Nat,List Char)
json s = go [<] 0 0 (unpack s) (ssAcc _)
