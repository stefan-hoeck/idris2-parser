module Text.WebIDL.Types.Member

import Data.SOP
import Derive.Prelude
import Text.WebIDL.Types.Argument
import Text.WebIDL.Types.Attribute
import Text.WebIDL.Types.Identifier
import Text.WebIDL.Types.StringLit
import Text.WebIDL.Types.Type

%language ElabReflection

||| Const ::
|||     const ConstType identifier = ConstValue ;
|||
||| ConstValue ::
|||     BooleanLiteral
|||     FloatLiteral
|||     integer
public export
record Const where
  constructor MkConst
  type  : ConstType
  name  : Identifier
  value : ConstValue

%runElab derive "Const" [Eq,Show,HasAttributes]

--------------------------------------------------------------------------------
--          Operation
--------------------------------------------------------------------------------

||| OperationName ::
|||     OperationNameKeyword
|||     identifier
|||
||| OperationNameKeyword ::
|||     includes
public export
record OperationName where
  constructor MkOpName
  value : String

%runElab derive "OperationName" [Eq,Show,HasAttributes]

||| Special ::
|||     getter
|||     setter
|||     deleter
public export
data Special = Getter | Setter | Deleter

%runElab derive "Special" [Eq,Show,HasAttributes]

||| RegularOperation ::
|||     Type OperationRest
|||
||| OperationRest ::
|||     OptionalOperationName ( ArgumentList ) ;
|||
||| OptionalOperationName ::
|||     OperationName
|||     ε
|||
||| SpecialOperation ::
|||     Special RegularOperation
|||
||| Operation ::
|||     RegularOperation
|||     SpecialOperation
public export
record Op a where
  constructor MkOp
  special : a
  type    : IdlType
  name    : Maybe OperationName
  args    : ArgumentList

%runElab derive "Op" [Eq,Show,HasAttributes]

public export
0 RegularOperation : Type
RegularOperation = Op ()

public export
0 SpecialOperation : Type
SpecialOperation = Op Special

public export
0 Operation : Type
Operation = Op (Maybe Special)

public export
regToOp : RegularOperation -> Operation
regToOp = { special := Nothing }

public export
specToOp : SpecialOperation -> Operation
specToOp = { special $= Just }

--------------------------------------------------------------------------------
--          Callbacks
--------------------------------------------------------------------------------


||| CallbackInterfaceMember ::
|||     Const
|||     RegularOperation
public export
0 CallbackInterfaceMember : Type
CallbackInterfaceMember = NS I [Const,RegularOperation]

||| CallbackInterfaceMembers ::
|||     ExtendedAttributeList CallbackInterfaceMember CallbackInterfaceMembers
|||     ε
public export
0 CallbackInterfaceMembers : Type
CallbackInterfaceMembers = List (Attributed CallbackInterfaceMember)

--------------------------------------------------------------------------------
--          Dictionary
--------------------------------------------------------------------------------

||| Inheritance ::
|||     : identifier
|||     ε
public export
0 Inheritance : Type
Inheritance = Maybe Identifier

||| DictionaryMemberRest ::
|||     required TypeWithExtendedAttributes identifier ;
|||     Type identifier Default ;
public export
data DictionaryMemberRest : Type where
  Required :  (attrs : ExtAttributeList)
           -> (type : IdlType)
           -> (name : Identifier)
           -> DictionaryMemberRest

  Optional :  (type  : IdlType)
           -> (name  : Identifier)
           -> (deflt : Default)
           -> DictionaryMemberRest

%runElab derive "DictionaryMemberRest" [Eq,Show,HasAttributes]

||| DictionaryMember ::
|||     ExtendedAttributeList DictionaryMemberRest
public export
0 DictionaryMember : Type
DictionaryMember = Attributed DictionaryMemberRest

||| DictionaryMembers ::
|||     DictionaryMember DictionaryMembers
|||     ε
public export
0 DictionaryMembers : Type
DictionaryMembers = List DictionaryMember

--------------------------------------------------------------------------------
--          Attributes
--------------------------------------------------------------------------------

public export
record Readonly a where
  constructor MkRO
  value : a

%runElab derive "Readonly" [Eq,Show,HasAttributes]

public export
record Inherit a where
  constructor MkI
  value : a

%runElab derive "Inherit" [Eq,Show,HasAttributes]

||| AttributeName ::
|||     AttributeNameKeyword
|||     identifier
|||
||| AttributeNameKeyword ::
|||     async
|||     required
public export
record AttributeName where
  constructor MkAttributeName
  value : String

%runElab derive "AttributeName" [Eq,Ord,Show,HasAttributes]

||| AttributeRest ::
|||     attribute TypeWithExtendedAttributes AttributeName ;
public export
record Attribute where
  constructor MkAttribute
  attrs : ExtAttributeList
  type  : IdlType
  name  : AttributeName

%runElab derive "Attribute" [Eq,Show,HasAttributes]

||| ReadWriteMaplike ::
|||     MaplikeRest
|||
||| MaplikeRest ::
|||     maplike < TypeWithExtendedAttributes , TypeWithExtendedAttributes > ;
public export
record Maplike where
  constructor MkMaplike
  fstTpe : Attributed IdlType
  sndTpe : Attributed IdlType

%runElab derive "Maplike" [Eq,Show,HasAttributes]

export
HasAttributes Maplike where
  attributes v = fst (v.fstTpe) ++ fst (v.sndTpe)

||| ReadWriteSetlike ::
|||     SetlikeRest
|||
||| SetlikeRest ::
|||     setlike < TypeWithExtendedAttributes > ;
public export
record Setlike where
  constructor MkSetlike
  type : Attributed IdlType

%runElab derive "Setlike" [Eq,Show,HasAttributes]

||| StringifierRest ::
|||     OptionalReadOnly AttributeRest
|||     RegularOperation
|||     ;
|||
||| Stringifier ::
|||     stringifier StringifierRest
public export
0 Stringifier : Type
Stringifier = NS I [Attribute, Readonly Attribute, RegularOperation,()]

||| StaticMember ::
|||     static StaticMemberRest
|||
||| StaticMemberRest ::
|||     OptionalReadOnly AttributeRest
|||     RegularOperation
public export
0 StaticMember : Type
StaticMember = NS I [Attribute, Readonly Attribute, RegularOperation]

--------------------------------------------------------------------------------
--          Namespace
--------------------------------------------------------------------------------

||| NamespaceMember ::
|||     RegularOperation
|||     readonly AttributeRest
public export
0 NamespaceMember : Type
NamespaceMember = NS I [RegularOperation, Readonly Attribute]

||| NamespaceMembers ::
|||     ExtendedAttributeList NamespaceMember NamespaceMembers
|||     ε
public export
0 NamespaceMembers : Type
NamespaceMembers = List (Attributed NamespaceMember)

--------------------------------------------------------------------------------
--          Interface
--------------------------------------------------------------------------------

||| Constructor ::
|||     constructor ( ArgumentList ) ;
public export
record Constructor where
  constructor MkConstructor
  args : ArgumentList

%runElab derive "Constructor" [Eq,Show,HasAttributes]

||| PartialInterfaceMember ::
|||     Const
|||     Operation
|||     Stringifier
|||     StaticMember
|||     Iterable
|||     AsyncIterable
|||     ReadOnlyMember
|||     ReadWriteAttribute
|||     ReadWriteMaplike
|||     ReadWriteSetlike
|||     InheritAttribute
|||
||| Iterable ::
|||     iterable < TypeWithExtendedAttributes OptionalType > ;
public export
data PartialInterfaceMember =
    IConst   Const
  | IOp      Operation
  | IStr     Stringifier
  | IStatic  StaticMember
  | IAttr    Attribute
  | IMap     Maplike
  | ISet     Setlike
  | IAttrRO  (Readonly Attribute)
  | IMapRO   (Readonly Maplike)
  | ISetRO   (Readonly Setlike)
  | IAttrInh (Inherit Attribute)
  | IIterable (Attributed IdlType) OptionalType
  | IAsync   (Attributed IdlType) OptionalType ArgumentList

%runElab derive "PartialInterfaceMember" [Eq,Show,HasAttributes]


||| MixinMember ::
|||     Const
|||     RegularOperation
|||     Stringifier
|||     OptionalReadOnly AttributeRest
public export
data MixinMember =
    MConst   Const
  | MOp      RegularOperation
  | MStr     Stringifier
  | MAttr    Attribute
  | MAttrRO  (Readonly Attribute)

%runElab derive "MixinMember" [Eq,Show,HasAttributes]


||| PartialInterfaceMembers ::
|||     ExtendedAttributeList PartialInterfaceMember PartialInterfaceMembers
|||     ε
public export
0 PartialInterfaceMembers : Type
PartialInterfaceMembers = List (Attributed PartialInterfaceMember)

||| InterfaceMember ::
|||     PartialInterfaceMember
|||     Constructor
public export
0 InterfaceMember : Type
InterfaceMember = NS I [Constructor,PartialInterfaceMember]


||| InterfaceMembers ::
|||     ExtendedAttributeList InterfaceMember InterfaceMembers
|||     ε
public export
0 InterfaceMembers : Type
InterfaceMembers = List (Attributed InterfaceMember)

||| MixinMembers ::
|||     ExtendedAttributeList MixinMember MixinMembers
|||     ε
public export
0 MixinMembers : Type
MixinMembers = List (Attributed MixinMember)

--------------------------------------------------------------------------------
--          Extractors
--------------------------------------------------------------------------------

namespace CallbackInterfaceMember
  export
  const : Attributed CallbackInterfaceMember -> Maybe Const
  const (_,Z x) = Just x
  const _       = Nothing

namespace Dictionary
  export
  optional : DictionaryMember -> Maybe Attribute
  optional (_, Required _ _ _) = Nothing
  optional (_, Optional t n _) =
    Just $ MkAttribute Nil t (MkAttributeName n.value)

  export
  required : DictionaryMember -> Maybe Attribute
  required (_, Required _ t n) =
    Just $ MkAttribute Nil t (MkAttributeName n.value)
  required (_, Optional _ _ _) = Nothing

namespace InterfaceMember
  export
  part :  (PartialInterfaceMember -> Maybe a)
       -> Attributed InterfaceMember
       -> Maybe a
  part f (_,(S $ Z $ p)) = f p
  part _ _               = Nothing

namespace MixinMember
  export
  const : Attributed MixinMember -> Maybe Const
  const (_,MConst x) = Just x
  const _            = Nothing

  export
  attrRO : Attributed MixinMember -> Maybe (Readonly Attribute)
  attrRO (_, (MAttrRO x)) = Just x
  attrRO _                = Nothing

  export
  attr : Attributed MixinMember -> Maybe Attribute
  attr (_, (MAttr x)) = Just x
  attr _              = Nothing

namespace NamespaceMember

  export
  attrRO : NamespaceMember -> Maybe (Readonly Attribute)
  attrRO (S $ Z x) = Just x
  attrRO (Z _)     = Nothing

namespace PartialInterfaceMember
  export
  const : PartialInterfaceMember -> Maybe Const
  const (IConst x) = Just x
  const _          = Nothing

  export
  attrRO : PartialInterfaceMember -> Maybe (Readonly Attribute)
  attrRO (IAttrRO x) = Just x
  attrRO _           = Nothing

  export
  attr : PartialInterfaceMember -> Maybe Attribute
  attr (IAttr x) = Just x
  attr _         = Nothing
