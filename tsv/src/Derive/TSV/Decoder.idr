module Derive.TSV.Decoder

import public Text.Parse.Manual
import public Text.Lex.Manual.Syntax
import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Top-level function declaration implementing the `decodeFrom` function for
||| the given data type.
export
decClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
decClaim vis fun p =
  let arg := p.applied
      tpe := piAll `({0 e : Type} -> Tok e ~(arg)) (allImplicits p "TSVDecoder")
   in simpleClaim vis fun tpe

||| Top-level declaration implementing the `TSVDecoder` interface for
||| the given data type.
export
decoderImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
decoderImplClaim v impl p = implClaimVis v impl (implType "TSVDecoder" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
decoderImplDef : (fun, impl : Name) -> Decl
decoderImplDef f i =
  def i [patClause (var i) (var "MkTSVDecoder" `app` var f)]

appArgs : TTImp -> List (BoundArg 0 Explicit) -> TTImp
appArgs t []                = t
appArgs t [BA _ [] _]       = `(Tok.(<*>) ~(t) decodeFrom)
appArgs t (BA _ [] _ :: xs) =
  appArgs `(Tok.(<*>) ~(t) (Tok.(<*) decodeFrom tab)) xs

decClause : Name -> Con n vs -> Clause
decClause f c =
  let sx := boundArgs explicit c.args []
   in patClause (var f) (appArgs `(Tok.pure ~(c.nameVar)) $ sx <>> [])

decDef : Name -> Con n vs -> Decl
decDef f c = def f [decClause f c]

enumClause : Con n vs -> Clause
enumClause c = patClause (c.namePrim) `(Just ~(c.nameVar))

enumDef : Name -> ParamTypeInfo -> Decl
enumDef f p =
  let catchAll := patClause implicitTrue `(Nothing)
      cls      := map enumClause p.info.cons ++ [catchAll]
   in def f [patClause (var f) `(refine str $ \x => ~(iCase `(x) implicitFalse cls))]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Semigroup` for a given data type.
export
TSVDecoderVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
TSVDecoderVis vis nms p =
  let fun  := funName p "decodeFrom"
      impl := implName p "TSVDecoder"
   in case p.info.cons of
        [c] =>
          Right
            [ TL (decClaim vis fun p) (decDef fun c)
            , TL (decoderImplClaim vis impl p) (decoderImplDef fun impl)
            ]
        _   =>
          case isEnum p.info of
            False => failRecord "TSVDecoder"
            True  =>
              Right
                [ TL (decClaim vis fun p) (enumDef fun p)
                , TL (decoderImplClaim vis impl p) (decoderImplDef fun impl)
            ]

||| Alias for `SemigroupVis Public`
export %inline
TSVDecoder : List Name -> ParamTypeInfo -> Res (List TopLevel)
TSVDecoder = TSVDecoderVis Public
