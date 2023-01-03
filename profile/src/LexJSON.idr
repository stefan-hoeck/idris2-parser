module LexJSON

import Derive.Prelude
import Text.Lex

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

exp : Shifter True Char
exp sc ('e' :: t) = intLitPlus (sc :< 'e') t ~> sh1
exp sc ('E' :: t) = intLitPlus (sc :< 'E') t ~> sh1
exp sc _          = Stop

dec : Shifter True Char
dec sc ('.' :: t) = digits (sc :< '.') t ~> sh1
dec _  _          = Stop

rest : Lexer
rest = Lift exp <|> (Lift dec <+> opt (Lift exp))

num : Lexer
num = intLitPlus <+> opt rest

export
json : TokenMap Token
json =
  [ (is ',', const TComma)
  , (stringLit, TStr . pack . (<>> []))
  , (is '[', const TBracketO)
  , (is ']', const TBracketC)
  , (is '{', const TBraceO)
  , (is '}', const TBraceC)
  , (is ':', const TColon)
  , (num, TNum . cast . pack . (<>> []))
  , (exact "null", const TNull)
  , (exact "true", const $ TBool True)
  , (exact "false", const $ TBool False)
  , (preds isSpace, const TSpace)
  ]
