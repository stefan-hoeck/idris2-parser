module Lex2JSON

import Derive.Prelude
import Text.Lex2

%language ElabReflection
%default total

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

exp : Lexer
exp sc ('e' :: '+' :: t) = digits (sc :< 'e' :< '+') t ~> cons1 ~> cons1
exp sc ('E' :: '+' :: t) = digits (sc :< 'E' :< '+') t ~> cons1 ~> cons1
exp sc ('e' :: '-' :: t) = digits (sc :< 'e' :< '-') t ~> cons1 ~> cons1
exp sc ('E' :: '-' :: t) = digits (sc :< 'E' :< '-') t ~> cons1 ~> cons1
exp sc ('e' :: t)        = digits (sc :< 'e') t ~> cons1
exp sc ('E' :: t)        = digits (sc :< 'E') t ~> cons1
exp sc t                 = digits sc t

dec : Lexer
dec sc ('.' :: t) = digits (sc :< '.') t ~> cons1
dec sc t          = digits sc t

rest : Lexer
rest = exp <|> (dec <+> opt exp)

num : Lexer
num = opt (oneOf "+-") <+> digits <+> (opt rest)

symbol : Lexer
symbol sc (',' :: t) = Res (sc :< ',') t %search
symbol sc ('[' :: t) = Res (sc :< '[') t %search
symbol sc (']' :: t) = Res (sc :< ']') t %search
symbol sc ('{' :: t) = Res (sc :< '{') t %search
symbol sc ('}' :: t) = Res (sc :< '}') t %search
symbol sc (':' :: t) = Res (sc :< ':') t %search
symbol _ _ = Stop

fromSymbol : SnocList Char -> Token
fromSymbol [< c] = case c of
  ',' => TComma
  ':' => TColon
  '[' => TBracketO
  ']' => TBracketC
  '{' => TBraceO
  _   => TBraceC
fromSymbol _ = TBraceC

export
json : TokenMap Token
json =
  [ (symbol, fromSymbol)
  , (spaces, const TSpace)
  , (stringLit, TStr . pack)
  , (num, TNum . cast . pack)
  , (exact "null", const TNull)
  , (exact "true", const $ TBool True)
  , (exact "false", const $ TBool False)
  ]
