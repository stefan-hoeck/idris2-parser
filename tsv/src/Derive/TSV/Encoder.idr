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

enumClause : Name -> Con n vs -> Clause
enumClause f c = patClause `(~(var f) sc ~(c.nameVar)) `(sc :< ~(c.namePrim))

export
encDef : Name -> Con n vs -> Decl
encDef f c = def f [encClause f c]

export
enumDef : Name -> ParamTypeInfo -> Decl
enumDef f c = def f (map (enumClause f) c.info.cons)

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

||| Generate declarations and implementations for `Semigroup` for a given data type.
export
TSVEncoderVis : Visibility -> List Name -> ParamTypeInfo -> Res (List TopLevel)
TSVEncoderVis vis nms p =
  let fun  := funName p "encodeOnto"
      impl := implName p "TSVEncoder"
   in case p.info.cons of
        [c] =>
           Right
             [ TL (encClaim vis fun p) (encDef fun c)
             , TL (encoderImplClaim vis impl p) (encoderImplDef fun impl)
             ]
        _   =>
          case isEnum p.info of
            False => failRecord "TSVEncoder"
            True  =>
              Right
                [ TL (encClaim vis fun p) (enumDef fun p)
                , TL (encoderImplClaim vis impl p) (encoderImplDef fun impl)
                ]

||| Alias for `SemigroupVis Public`
export %inline
TSVEncoder : List Name -> ParamTypeInfo -> Res (List TopLevel)
TSVEncoder = TSVEncoderVis Public
