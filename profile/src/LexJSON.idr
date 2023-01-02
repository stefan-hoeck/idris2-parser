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

exp : Lexer
exp = like 'e' <+> opt (oneOf "+-") <+> digits

dec : Lexer
dec = is '.' <+> digits

rest : Lexer
rest = exp <|> (dec <+> opt exp)

num : Lexer
num = opt (oneOf "+-") <+> digits <+> (opt rest)

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
