module Derive.TSV.Encoder

import Language.Reflection.Util

%default total

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| Top-level function declaration implementing the `encodeOnto` function for
||| the given data type.
export
encClaim : Visibility -> (fun : Name) -> (p : ParamTypeInfo) -> Decl
encClaim vis fun p =
  let arg := p.applied
      tpe := piAll `(SnocList String -> ~(arg) -> SnocList String) (allImplicits p "TSVEncoder")
   in simpleClaim vis fun tpe

||| Top-level declaration implementing the `TSVEncoder` interface for
||| the given data type.
export
encoderImplClaim : Visibility -> (impl : Name) -> (p : ParamTypeInfo) -> Decl
encoderImplClaim v impl p = implClaimVis v impl (implType "TSVEncoder" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

export
encoderImplDef : (fun, impl : Name) -> Decl
encoderImplDef f i =
  def i [patClause (var i) (var "MkTSVEncoder" `app` var f)]

appArgs : TTImp -> List (BoundArg 1 Explicit) -> TTImp
appArgs t []                 = t
appArgs t (BA _ [x] _ :: xs) = appArgs `(encodeOnto ~(t) ~(varStr x)) xs

encClause : Name -> Con n vs -> Clause
encClause f c =
  let xs := freshNames "x" c.arty
      cx := bindCon c xs
      sx := boundArgs explicit c.args [xs]
   in patClause `(~(var f) sc ~(cx)) (appArgs `(sc) $ sx <>> [])

export
encDef : Name -> Con n vs -> Decl
encDef f c = def f [encClause f c]

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Semigroup` for a given data type.
export
TSVEncoderVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
TSVEncoderVis vis nms p = case p.info.cons of
  [c] =>
    let fun  := funName p "encodeOnto"
        impl := implName p "TSVEncoder"
     in Right [ TL (encClaim vis fun p) (encDef fun c)
              , TL (encoderImplClaim vis impl p) (encoderImplDef fun impl)
              ]
  _   => failRecord "TSVEncoder"

||| Alias for `SemigroupVis Public`
export %inline
TSVEncoder : List Name -> ParamTypeInfo -> Res (List TopLevel)
TSVEncoder = TSVEncoderVis Public
