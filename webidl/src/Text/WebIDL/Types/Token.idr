module Text.WebIDL.Types.Token

import Derive.Prelude
import Text.WebIDL.Types.Identifier
import Text.WebIDL.Types.Numbers
import Text.WebIDL.Types.StringLit
import Text.WebIDL.Types.Symbol

%default total

%language ElabReflection

public export
data IdlError : Type where
  EmptyAttributeList : IdlError

%runElab derive "IdlError" [Show,Eq]

export
Interpolation IdlError where
  interpolate EmptyAttributeList = "Empty attribute list"

||| Text tokens in the WebIDL grammar. The `Invalid` token
||| is not recognized by any parser and will lead to a
||| failure during parsing.
public export
data IdlToken : Type where
  ||| A string literal
  SLit      : StringLit  -> IdlToken

  ||| An integer literal (in decimal, hexadecimal, or
  ||| octal representation)
  ILit      : IntLit     -> IdlToken

  ||| A floating point literal
  FLit      : FloatLit   -> IdlToken

  ||| Any valid identifier that is not also a
  ||| keyword.
  Ident     : Identifier -> IdlToken

  ||| A WebIDL keyword
  Key       : Keyword    -> IdlToken

  ||| A single symbol character (or an ellipsis: ...)
  Other     : Symbol     -> IdlToken

  ||| Single or multiline comment
  Comment   : IdlToken

  ||| A sequence of whitespace characters
  Space     : IdlToken

%runElab derive "IdlToken" [Eq,Show]

export
Interpolation IdlToken where
  interpolate (SLit x)  = interpolate x
  interpolate (ILit x)  = interpolate x
  interpolate (FLit x)  = interpolate x
  interpolate (Ident x) = interpolate x
  interpolate (Key x)   = interpolate x
  interpolate (Other x) = interpolate x
  interpolate Comment   = "<comment>"
  interpolate Space     = "<space>"
