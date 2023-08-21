module Text.WebIDL.Types.Definition

import Data.List.Elem
import Data.SOP
import Derive.Prelude
import Text.WebIDL.Types.Attribute
import Text.WebIDL.Types.Argument
import Text.WebIDL.Types.Identifier
import Text.WebIDL.Types.Member
import Text.WebIDL.Types.StringLit
import Text.WebIDL.Types.Type

%hide Language.Reflection.TT.Namespace
%language ElabReflection

||| CallbackRest ::
|||     identifier = Type ( ArgumentList ) ;
public export
record Callback where
  constructor MkCallback
  attributes : ExtAttributeList
  name       : Identifier
  type       : IdlType
  args       : ArgumentList

%runElab derive "Callback" [Eq,Show,HasAttributes]

||| CallbackRestOrInterface ::
|||     CallbackRest
|||     interface identifier { CallbackInterfaceMembers } ;
public export
record CallbackInterface where
  constructor MkCallbackInterface
  attributes : ExtAttributeList
  name       : Identifier
  members    : CallbackInterfaceMembers

%runElab derive "CallbackInterface" [Eq,Show,HasAttributes]

||| Dictionary ::
|||     dictionary identifier Inheritance { DictionaryMembers } ;
public export
record Dictionary where
  constructor MkDictionary
  attributes : ExtAttributeList
  name       : Identifier
  inherits   : Inheritance
  members    : DictionaryMembers

%runElab derive "Dictionary" [Eq,Show,HasAttributes]

||| Enum ::
|||     enum identifier { EnumValueList } ;
|||
||| EnumValueList ::
|||     string EnumValueListComma
|||
||| EnumValueListComma ::
|||     , EnumValueListString
|||     ε
|||
||| EnumValueListString ::
|||     string EnumValueListComma
|||     ε
public export
record Enum where
  constructor MkEnum
  attributes : ExtAttributeList
  name       : Identifier
  values     : List1 StringLit

%runElab derive "Enum" [Eq,Show,HasAttributes]

||| IncludesStatement ::
|||     identifier includes identifier ;
public export
record Includes where
  constructor MkIncludes
  attributes : ExtAttributeList
  name       : Identifier
  includes   : Identifier

%runElab derive "Includes" [Eq,Show,HasAttributes]

||| InterfaceRest ::
|||     identifier Inheritance { InterfaceMembers } ;
public export
record Interface where
  constructor MkInterface
  attributes : ExtAttributeList
  name       : Identifier
  inherits   : Inheritance
  members    : InterfaceMembers

%runElab derive "Interface" [Eq,Show,HasAttributes]

||| MixinRest ::
|||     mixin identifier { MixinMembers } ;
public export
record Mixin where
  constructor MkMixin
  attributes : ExtAttributeList
  name       : Identifier
  members    : MixinMembers

%runElab derive "Mixin" [Eq,Show,HasAttributes]

||| Namespace ::
|||     namespace identifier { NamespaceMembers } ;
public export
record Namespace where
  constructor MkNamespace
  attributes : ExtAttributeList
  name       : Identifier
  members    : NamespaceMembers

%runElab derive "Namespace" [Eq,Show,HasAttributes]

||| Typedef ::
|||     typedef TypeWithExtendedAttributes identifier ;
public export
record Typedef where
  constructor MkTypedef
  attributes     : ExtAttributeList
  typeAttributes : ExtAttributeList
  type           : IdlType
  name           : Identifier

%runElab derive "Typedef" [Eq,Show,HasAttributes]

||| PartialDictionary ::
|||     dictionary identifier { DictionaryMembers } ;
public export
record PDictionary where
  constructor MkPDictionary
  attributes : ExtAttributeList
  name       : Identifier
  members    : DictionaryMembers

%runElab derive "PDictionary" [Eq,Show,HasAttributes]

||| PartialInterfaceRest ::
|||     identifier { PartialInterfaceMembers } ;
public export
record PInterface where
  constructor MkPInterface
  attributes : ExtAttributeList
  name       : Identifier
  members    : PartialInterfaceMembers

%runElab derive "PInterface" [Eq,Show,HasAttributes]

||| MixinRest ::
|||     mixin identifier { MixinMembers } ;
public export
record PMixin where
  constructor MkPMixin
  attributes : ExtAttributeList
  name       : Identifier
  members    : MixinMembers

%runElab derive "PMixin" [Eq,Show,HasAttributes]

||| Namespace ::
|||     namespace identifier { NamespaceMembers } ;
public export
record PNamespace where
  constructor MkPNamespace
  attributes : ExtAttributeList
  name       : Identifier
  members    : NamespaceMembers

%runElab derive "PNamespace" [Eq,Show,HasAttributes]

public export
DefTypes : List Type
DefTypes =
  [ Callback
  , CallbackInterface
  , Dictionary
  , Enum
  , Includes
  , Interface
  , Mixin
  , Namespace
  , Typedef
  ]

public export
PartTypes : List Type
PartTypes = [PDictionary, PInterface, PMixin, PNamespace]

||| Definition ::
|||     CallbackOrInterfaceOrMixin
|||     Namespace
|||     Partial
|||     Dictionary
|||     Enum
|||     Typedef
|||     IncludesStatement
||| CallbackOrInterfaceOrMixin ::
|||     callback CallbackRestOrInterface
|||     interface InterfaceOrMixin
|||
||| InterfaceOrMixin ::
|||     InterfaceRest
|||     MixinRest
public export
Definition : Type
Definition = NS I DefTypes

public export
0 Definitions : Type
Definitions = NP List DefTypes

||| PartialDefinition ::
|||     interface PartialInterfaceOrPartialMixin
|||     PartialDictionary
|||     Namespace
|||
||| PartialInterfaceOrPartialMixin ::
|||     PartialInterfaceRest
|||     MixinRest
public export
Part : Type
Part = NS I PartTypes

public export
accumNs : {ts : _} -> List (NS I ts) -> NP List ts
accumNs = foldl (\np,ns => hliftA2 (++) (toNP ns) np) hempty

public export
0 PartOrDef : Type
PartOrDef = NS I [Part,Definition]

public export
0 PartsAndDefs : Type
PartsAndDefs = NP List [Part,Definition]

public export
defs : PartsAndDefs -> Definitions
defs [_,d] = accumNs d

--------------------------------------------------------------------------------
--          Domain
--------------------------------------------------------------------------------

update : Eq k => (b -> b) -> k -> (b -> k) -> List b -> List b
update f k bk = map (\b => if bk b == k then f b else b)

mergeDict : PDictionary -> Dictionary -> Dictionary
mergeDict d = { members $= (++ d.members) }

mergeIface : PInterface -> Interface -> Interface
mergeIface i = { members $= (++ map to i.members) }

  where
    to : (a,b) -> (a, NS I [c,b])
    to (x, y) = (x, inject y)

mergeMixin : PMixin -> Mixin -> Mixin
mergeMixin m = { members $= (++ m.members) }

mergeNamespace : PNamespace -> Namespace -> Namespace
mergeNamespace n = { members $= (++ n.members) }

public export
record Domain where
  constructor MkDomain
  domain              : String
  callbacks           : List Callback
  callbackInterfaces  : List CallbackInterface
  dictionaries        : List Dictionary
  enums               : List Enum
  includeStatements   : List Includes
  interfaces          : List Interface
  mixins              : List Mixin
  namespaces          : List Namespace
  typedefs            : List Typedef

%runElab derive "Domain" [Eq,Show,HasAttributes]

applyPart : Domain -> Part -> Domain
applyPart d (Z v) =
  { dictionaries $= update (mergeDict v) v.name name } d
applyPart d (S $ Z v) =
  { interfaces $= update (mergeIface v) v.name name } d
applyPart d (S $ S $ Z v) =
  { mixins $= update (mergeMixin v) v.name name } d
applyPart d (S $ S $ S $ Z v) =
  { namespaces $= update (mergeNamespace v) v.name name } d

export
toDomains : List (String,PartsAndDefs) -> List Domain
toDomains ps =
  let defs = map (\(s,pad) => fromNP s (defs pad)) ps
      prts = concatMap (\(_,pad) => get Part pad) ps
   in map (\d => foldl applyPart d prts) defs

  where
    fromNP : String -> Definitions -> Domain
    fromNP s [c,ci,d,e,ic,it,m,n,t] = MkDomain s c ci d e ic it m n t
