module Text.Lex.Idris2.Package

import Core.Name.Namespace.Extra
import Derive.Prelude
import Text.Lex.Idris2.Common

%hide Language.Reflection.TT.Namespace
%default total
%language ElabReflection

public export
data Token
  = Comment String
  | EndOfInput
  | Equals
  | DotSepIdent (Maybe Namespace) String
  | Separator
  | Dot
  | LTE
  | GTE
  | LT
  | GT
  | EqOp
  | AndOp
  | Space
  | StringLit String
  | IntegerLit Integer

%runElab derive "Token" [Show, Eq]

equals : Lexer
equals = is '='

separator : Lexer
separator = is ','

dot : Lexer
dot = is '.'

lte : Lexer
lte = is '<' <+> is '='

gte : Lexer
gte = is '>' <+> is '='

lt : Lexer
lt = is '<'

gt : Lexer
gt = is '>'

eqop : Lexer
eqop = is '=' <+> is '='

andop : Lexer
andop = is '&' <+> is '&'

rawTokens : TokenMap Token
rawTokens =
  [ (comment, Comment . pack . drop 2 . (<>> []))
  , (namespacedIdent, uncurry DotSepIdent . mkNamespacedIdent)
  , (identAllowDashes, DotSepIdent Nothing . cast)
  , (separator, const Separator)
  , (dot, const Dot)
  , (lte, const LTE)
  , (gte, const GTE)
  , (lt, const LT)
  , (gt, const GT)
  , (eqop, const EqOp)
  , (andop, const AndOp)
  , (equals, const Equals)
  , (spaces, const Space)
  , (stringLit, StringLit . stripQuotes)
  , (intLit, IntegerLit . cast . cast {to = String})
  ]

keep : Token -> Bool
keep (Comment _) = False
keep Space       = False
keep _           = True

export
lex : String -> Either (Nat, Nat, String) (List (Bounded Token))
lex str =
  case lex (Match rawTokens) str of
   TR l c st _ [] _ =>
     let eoi := B EndOfInput (BS l c l c)
      in Right . filter (keep . val) $ st <>> [eoi]
   TR l c _ _ cs _ => Left (l, c, pack cs)
