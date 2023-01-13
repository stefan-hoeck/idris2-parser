module LexJSON

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
data Token : Type where
  TBracketO : Token
  TBracketC : Token
  TBraceO   : Token
  TBraceC   : Token
  TComma    : Token
  TColon    : Token
  TNull     : Token
  TBool     : Bool   -> Token
  TNum      : Double -> Token
  TStr      : String -> Token
  TSpace    : Token

%runElab derive "Token" [Show,Eq]

str :
     SnocList Char
  -> (cs : List Char)
  -> {auto prf : Tail True cs cs'}
  -> DirectRes cs' Token
str sc ('\\' :: '"'  :: xs) = str (sc :< '"') xs
str sc ('\\' :: '\\' :: xs) = str (sc :< '\\') xs
str sc ('"'  ::        xs) = Succ (TStr $ pack sc) xs
str sc (c    ::        xs) = str (sc :< c) xs
str sc []                  = Fail

toNum : DirectRes cs (SnocList Char) -> DirectRes cs Token
toNum (Succ x ds) = Succ (TNum $ cast $ pack x) ds
toNum Fail        = Fail

digs,rest,dot,exp,exp1,exp2,exp3 :
     SnocList Char
  -> (cs : List Char)
  -> {auto prf : Tail True cs cs'}
  -> DirectRes cs' (SnocList Char)

exp3 sc (d :: ds) = if isDigit d then exp3 (sc :< d) ds else Succ sc (d :: ds)
exp3 sc []        = Succ sc []

exp2 sc (d :: ds) = if isDigit d then exp3 (sc :< d) ds else Fail
exp2 sc []        = Fail

exp1 sc ('-' :: ds) = exp1 (sc :< '-') ds
exp1 sc ('+' :: ds) = exp1 (sc :< '+') ds
exp1 sc ds          = exp2 sc ds

exp sc ('e' :: ds) = exp1 (sc :< 'e') ds
exp sc ('E' :: ds) = exp1 (sc :< 'e') ds
exp sc ds          = Succ sc ds

dot sc (d :: ds) = if isDigit d then dot (sc :< d) ds else exp sc (d :: ds)
dot sc [] = Succ sc []

rest sc ('.' :: d :: ds) = if isDigit d then dot (sc :< '.' :< d) ds else Fail
rest sc ds               = exp sc ds

digs sc (d :: ds) = if isDigit d then digs (sc :< d) ds else rest sc (d :: ds)
digs sc []        = Succ sc []

num :
     SnocList Char
  -> (cs : List Char)
  -> {auto prf : Tail False cs cs'}
  -> DirectRes cs' (SnocList Char)
num sc ('0' :: xs) = rest (sc :< '0') xs
num sc (d :: xs)   = if isDigit d then digs (sc :< d) xs else Fail
num sc []          = Fail

term : (cs : List Char) -> DirectRes cs Token
term (x :: xs) = case x of
  ',' => Succ TComma xs
  '"' => str [<] xs
  ':' => Succ TColon xs
  'n' => case xs of
    'u' :: 'l' :: 'l' :: t => Succ TNull t
    _                      => Fail
  't' => case xs of
    'r' :: 'u' :: 'e' :: t => Succ (TBool True) t
    _                      => Fail
  'f' => case xs of
    'a' :: 'l' :: 's' :: 'e' :: t => Succ (TBool False) t
    _                             => Fail
  '-' => toNum $ num [<'-'] xs
  d   => toNum $ num [<] (d :: xs)
  
term []        = Fail

brace : SnocList Char -> Token
brace [<'['] = TBracketO
brace [<'{'] = TBraceO
brace [<']'] = TBracketC
brace _      = TBraceC

tag : SnocList Char -> Paren
tag [<'['] = Bracket
tag _      = Brace

close : Paren -> Lexer
close Bracket = is ']'
close Brace   = is '}'

opn : Lexer
opn = Lift $ \sc,cs => case cs of
  '[' :: xs => Res _ xs sh1
  '{' :: xs => Res _ xs sh1
  _         => Stop

export
json : Tokenizer Token
json =
      Direct term
  <|> Compose opn brace tag (\_ => json) close brace
  <|> Match [(spaces, const TSpace)]
