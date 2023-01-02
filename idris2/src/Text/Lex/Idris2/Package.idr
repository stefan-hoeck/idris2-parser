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

stripQuotes : SnocList Char -> String
stripQuotes (sx :< _) = case sx <>> [] of
  _ :: t => pack t
  _      => ""
stripQuotes [<]       = ""

rawTokens : TokenMap Token
rawTokens =
  [ (comment, \sc => Comment $ pack . drop 2 $ sc <>> [])
  , (namespacedIdent, uncurry DotSepIdent . mkNamespacedIdent)
  , (identAllowDashes, DotSepIdent Nothing . pack . (<>> []))
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
  , (intLit, IntegerLit . cast . pack)
  ]

keep : Token -> Bool
keep (Comment _) = False
keep Space       = False
keep _           = True

export
lex : String -> Either (Nat, Nat, String) (List (WithBounds Token))
lex str =
  case lex rawTokens str of
   (st, (l, c, [])) =>
     let eoi := MkBounded EndOfInput (Just $ MkBounds l c l c)
      in Right . filter (keep . val) $ st <>> [eoi]
   (_, (l,c,cs))               => Left (l, c, pack cs)
