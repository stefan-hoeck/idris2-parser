module Text.WebIDL.Types.Attribute

import Data.List1
import Derive.Prelude
import Language.Reflection.Util
import Data.SOP
import Text.WebIDL.Types.Numbers
import Text.WebIDL.Types.StringLit
import Text.WebIDL.Types.Identifier
import Text.WebIDL.Types.Symbol

%default total
%language ElabReflection

public export
isParenOrQuote : Char -> Bool
isParenOrQuote '(' = True
isParenOrQuote ')' = True
isParenOrQuote '[' = True
isParenOrQuote ']' = True
isParenOrQuote '{' = True
isParenOrQuote '}' = True
isParenOrQuote '"' = True
isParenOrQuote _   = False

public export
isCommaOrParenOrQuote : Char -> Bool
isCommaOrParenOrQuote ',' = True
isCommaOrParenOrQuote c   = isParenOrQuote c

public export
0 Other : Type
Other = NS I [IntLit,FloatLit,StringLit,Identifier,Keyword,Symbol]

||| ExtendedAttributeInner ::
public export
data EAInner : Type where
  |||   ε
  Nil : EAInner
  
  |||   ( ExtendedAttributeInner ) ExtendedAttributeInner
  |||   [ ExtendedAttributeInner ] ExtendedAttributeInner
  |||   { ExtendedAttributeInner } ExtendedAttributeInner
  (::) : (head : Either EAInner Other) -> (eai : EAInner) -> EAInner

%runElab derive "EAInner" [Eq,Show]

public export
0 InnerOrOther : Type
InnerOrOther = Either EAInner Other

public export
innerAttribute : SnocList InnerOrOther -> EAInner -> EAInner
innerAttribute [<]       x = x
innerAttribute (sx :< y) x = innerAttribute sx $ y :: x

namespace EAInner

  ||| Number of `Other`s.
  public export
  size : EAInner -> Nat
  size (Left eai :: t) = size eai + size t
  size (Right _ :: t)  = 1 + size t
  size []              = 0

  ||| Number of `Other`s.
  public export
  leaves : EAInner -> Nat
  leaves (Left eai :: t) = leaves eai + leaves t
  leaves (Right _ :: t)  = 1 + leaves t
  leaves []              = 1

  ||| Number of `Other`s.
  public export
  depth : EAInner -> Nat
  depth (Left eai :: t) = 1 + (depth eai `max` depth t)
  depth (Right _ :: t)  = 1 + depth t
  depth []              = 0

||| ExtendedAttributeRest ::
|||   ExtendedAttribute
|||   ε
|||
||| ExtendedAttribute ::
public export
data ExtAttribute : Type where
  ||| ( ExtendedAttributeInner ) ExtendedAttributeRest
  ||| [ ExtendedAttributeInner ] ExtendedAttributeRest
  ||| { ExtendedAttributeInner } ExtendedAttributeRest
  ||| Other ExtendedAttributeRest
  Last : InnerOrOther -> ExtAttribute
  Cons : InnerOrOther -> ExtAttribute -> ExtAttribute

%runElab derive "ExtAttribute" [Eq,Show]

public export
extAttribute : SnocList InnerOrOther -> ExtAttribute -> ExtAttribute
extAttribute [<]       x = x
extAttribute (sx :< y) x = extAttribute sx $ Cons y x

namespace ExtAttribute

  ||| Number of `Other`s.
  public export
  size : ExtAttribute -> Nat
  size (Cons (Left i) r)  = size i + size r
  size (Cons (Right _) r) = 1 + size r
  size (Last (Left i))    = size i
  size (Last (Right _))   = 1

  ||| Number of leaves (unlike `size`, this includes empty leaves)
  public export
  leaves : ExtAttribute -> Nat
  leaves (Cons (Left i) r)  = leaves i + leaves r
  leaves (Cons (Right _) r) = 1 + leaves r
  leaves (Last (Left i))    = leaves i + 1
  leaves (Last (Right _))   = 2

  ||| Number of `Other`s.
  public export
  depth : ExtAttribute -> Nat
  depth (Cons (Left i) r)  = 1 + (depth i `max` depth r)
  depth (Cons (Right _) r) = 1 + depth r
  depth (Last (Left i))    = 1 + depth i
  depth (Last (Right _))   = 1


||| ExtendedAttributeList ::
|||   [ ExtendedAttribute ExtendedAttributes ]
|||   ε
|||
||| ExtendedAttributes ::
|||   , ExtendedAttribute ExtendedAttributes
|||   ε
public export
ExtAttributeList : Type
ExtAttributeList = List ExtAttribute

||| TypeWithExtendedAttributes ::
|||     ExtendedAttributeList Type
public export
Attributed : Type -> Type
Attributed a = (ExtAttributeList, a)

public export
interface HasAttributes a where
  constructor MkHasAttributes
  attributes : a -> ExtAttributeList

public export
HasAttributes () where
  attributes = const Nil

public export
HasAttributes String where
  attributes = const Nil

public export %inline
HasAttributes Identifier where
  attributes = const Nil

public export %inline
HasAttributes Bool where
  attributes = const Nil

public export %inline
HasAttributes FloatLit where
  attributes = const Nil

public export %inline
HasAttributes IntLit where
  attributes = const Nil

public export %inline
HasAttributes StringLit where
  attributes = const Nil

public export %inline
(HasAttributes a, HasAttributes b) => HasAttributes (a,b) where
  attributes (x,y) = attributes x ++ attributes y

public export %inline
HasAttributes ExtAttribute where
  attributes = pure

public export %inline
HasAttributes a => HasAttributes (Maybe a) where
  attributes = maybe Nil attributes

public export %inline
HasAttributes a => HasAttributes (List a) where
  attributes x = x >>= attributes

public export %inline
HasAttributes a => HasAttributes (List1 a) where
  attributes = attributes . forget

--------------------------------------------------------------------------------
--          Deriving HasAttributes
--------------------------------------------------------------------------------

public export
(all : NP HasAttributes ts) => HasAttributes (NP I ts) where
  attributes = hcconcatMap HasAttributes attributes

public export
(all : NP HasAttributes ts) => HasAttributes (NS I ts) where
  attributes = hcconcatMap HasAttributes attributes

public export
(all : POP HasAttributes ts) => HasAttributes (SOP I ts) where
  attributes = hcconcatMap HasAttributes attributes

--------------------------------------------------------------------------------
--          Claims
--------------------------------------------------------------------------------

||| General type of a `attributes` function with the given list
||| of implicit and auto-implicit arguments, plus the given argument type
||| to be displayed.
export
generalAttrType : (implicits : List Arg) -> (arg : TTImp) -> TTImp
generalAttrType is arg = piAll `(~(arg) -> ExtAttributeList) is

||| Top-level function declaration implementing the `attrbutes` function for
||| the given data type.
export
attrClaim : (fun : Name) -> (p : ParamTypeInfo) -> Decl
attrClaim fun p =
  let arg := p.applied
      tpe := generalAttrType (allImplicits p "HasAttributes") arg
   in public' fun tpe

||| Top-level declaration of the `HasAttributes`
||| implementation for the given data type.
export
attrImplClaim : (impl : Name) -> (p : ParamTypeInfo) -> Decl
attrImplClaim impl p = implClaim impl (implType "HasAttributes" p)

--------------------------------------------------------------------------------
--          Definitions
--------------------------------------------------------------------------------

||| Top-level definition of the `Show` implementation for the given data type.
export
attrImplDef : (fun, impl : Name) -> Decl
attrImplDef f i =
  def i [patClause (var i) (var "MkHasAttributes" `app` var f)]

parameters (nms : List Name)
  ttimp : BoundArg 1 Regular -> TTImp
  ttimp (BA (MkArg _  _ _ t) [x] _) = assertIfRec nms t `(attributes ~(var x))

  rsh : SnocList TTImp -> TTImp
  rsh [<] = `(Nil)
  rsh st  = `(listBind ~(listOf st) id)

  export
  attrClauses : (fun : Name) -> TypeInfo -> List Clause
  attrClauses fun ti = map clause ti.cons

    where
      clause : Con ti.arty ti.args -> Clause
      clause c =
        let ns  := freshNames "x" c.arty
            bc  := bindCon c ns
            lhs := var fun `app` bc
            st  := ttimp <$> boundArgs regular c.args [ns]
         in patClause lhs (rsh st)

  export
  attrDef : Name -> TypeInfo -> Decl
  attrDef fun ti = def fun (attrClauses fun ti)

--------------------------------------------------------------------------------
--          Deriving
--------------------------------------------------------------------------------

namespace Derive

  ||| Generate declarations and implementations for `HasAttributes`
  ||| for a given data type.
  export
  HasAttributes : List Name -> ParamTypeInfo -> Res (List TopLevel)
  HasAttributes nms p =
    let fun  := funName p "attributes"
        impl := implName p "HasAttributes"
     in Right
          [ TL (attrClaim fun p) (attrDef nms fun p.info)
          , TL (attrImplClaim impl p) (attrImplDef fun impl)
          ]

--------------------------------------------------------------------------------
--          Tests and Proofs
-----------------------------------------------------------------------------

isParenTrue : all Attribute.isParenOrQuote (unpack "(){}[]\"") = True
isParenTrue = Refl

isParenFalse : any Attribute.isParenOrQuote (unpack "=!?><:;,.-_") = False
isParenFalse = Refl

isCommaOrParenTrue : all Attribute.isCommaOrParenOrQuote (unpack ",(){}[]\"") = True
isCommaOrParenTrue = Refl

isCommaOrParenFalse : any Attribute.isCommaOrParenOrQuote (unpack "=!?><:;.-_") = False
isCommaOrParenFalse = Refl
