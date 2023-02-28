module Text.WebIDL.Encoder

import Data.SOP
import Data.List
import Data.String
import Text.WebIDL.Types

%default total

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

public export
0 Encoder : Type -> Type
Encoder a = a -> String

runEnc : forall a . Encoder a -> a -> String
runEnc = apply

inParens : Encoder a -> Encoder a
inParens f a = "(" ++ f a ++ ")"

inBrackets : Encoder a -> Encoder a
inBrackets f a = "[" ++ f a ++ "]"

inBraces : Encoder a -> Encoder a
inBraces f a = "{" ++ f a ++ "}"

inAngles : Encoder a -> Encoder a
inAngles f a = "<" ++ f a ++ ">"

emaybe : Encoder a -> Encoder (Maybe a)
emaybe f = maybe "" f

sepList' : (sep : String) -> List String -> String
sepList' sep = concat . intersperse sep

sepList : (sep : String) -> Encoder a -> Encoder (List a)
sepList sep f = sepList' sep . map f

emptyIfNull : Foldable f =>  Encoder (f a) -> Encoder (f a)
emptyIfNull f as = if null as then "" else f as

spaced : List String -> String
spaced = concat . intersperse " "

--------------------------------------------------------------------------------
--          Attribute
--------------------------------------------------------------------------------

export
other : Encoder Other
other = collapseNS
      . hliftA2 runEnc [interpolate,interpolate,interpolate,interpolate,interpolate,interpolate]

export
eaInner : Encoder EAInner
eaInner [] = ""
eaInner (Left ip :: eai) = "(" ++ eaInner ip ++ ") " ++ eaInner eai
eaInner (Right o :: eai) = other o ++ " " ++ eaInner eai

export
extAttribute : Encoder ExtAttribute
extAttribute (Last (Left i))    = "(" ++ eaInner i ++ ")"
extAttribute (Last (Right o))   = other o
extAttribute (Cons (Left i) r)  = "(" ++ eaInner i ++ ") " ++ extAttribute r
extAttribute (Cons (Right o) r) = other o ++ " " ++ extAttribute r

export
attributes : Encoder ExtAttributeList
attributes = emptyIfNull . inBrackets $ sepList "," extAttribute

export
attributed : Encoder a -> Encoder (Attributed a)
attributed f (as,a) = attributes as ++ " " ++ f a

--------------------------------------------------------------------------------
--          Type
--------------------------------------------------------------------------------

export
intType : Encoder IntType
intType Short    = "short"
intType Long     = "long"
intType LongLong = "long long"

export
floatType : Encoder FloatType
floatType Float = "float"
floatType Dbl   = "double"

export
primitive : Encoder PrimitiveType
primitive (Unsigned x)     = "unsigned " ++ intType x
primitive (Signed x)       = intType x
primitive (Unrestricted x) = "unrestricted " ++ floatType x
primitive (Restricted x)   = floatType x
primitive Undefined        = "undefined"
primitive Boolean          = "boolean"
primitive Byte             = "byte"
primitive Octet            = "octet"
primitive BigInt           = "bigint"

export
constType : Encoder ConstType
constType (CP x) = primitive x
constType (CI x) = interpolate x

export
idlType : Encoder IdlType

export
unionMember : Encoder UnionMemberType

unionList : SnocList String -> List UnionMemberType -> String

export
union : Encoder UnionType

export
distinguishable : Encoder Distinguishable

idlType Any         = "any"
idlType (D $ MaybeNull x) = distinguishable x ++ "?"
idlType (D $ NotNull x)   = distinguishable x
idlType (U $ MaybeNull x) = union x ++ "?"
idlType (U $ NotNull x)   = union x
idlType (Promise x) = "Promise <" ++ idlType x ++ ">"

unionMember (MkUnionMember a x) =
  attributes a ++ " " ++ distinguishable x

union (UT fst snd rest) = unionList [< unionMember fst, unionMember snd] rest

unionList ss [] = "(" ++ concat (intersperse " or " (ss <>> [])) ++ ")"
unionList ss (h::t) = unionList (ss :< unionMember h) t

distinguishable (P x) = primitive x
distinguishable (S x) = show x
distinguishable (I x) = "\{x}"
distinguishable (B x) = show x
distinguishable (Sequence a x) =
  "sequence <" ++ attributes a ++  idlType x ++ ">"
distinguishable (FrozenArray a x) =
  "FrozenArray <" ++ attributes a ++  idlType x ++ ">"
distinguishable (ObservableArray a x) =
  "ObservableArray <" ++ attributes a ++  idlType x ++ ">"
distinguishable (Record x a y) =
  "record<" ++ show x ++ "," ++ attributes a ++ idlType y ++ ">"
distinguishable Object = "object"
distinguishable Symbol = "symbol"

optionalType : Encoder OptionalType
optionalType Nothing = ""
optionalType (Just (a,x)) = "," ++ attributes a ++ idlType x

--------------------------------------------------------------------------------
--          Arguments
--------------------------------------------------------------------------------

export
constValue : Encoder ConstValue
constValue (B True)  = "true"
constValue (B False) = "false"
constValue (F x)     = "\{x}"
constValue (I x)     = "\{x}"

export
defaultV : Encoder Default
defaultV None      = ""
defaultV EmptyList = "= []"
defaultV EmptySet  = "= {}"
defaultV Null      = "= null"
defaultV (S x)     = "= " ++ "\{x}"
defaultV (C x)     = "= " ++ constValue x

arg : Encoder Arg
arg (MkArg as t n) = spaced [attributes as, idlType t, n.value]

vararg : Encoder Arg
vararg (MkArg as t n) = spaced [attributes as, idlType t ++ "...", n.value]

optArg : Encoder OptArg
optArg (MkOptArg as tas t n d) = spaced [ attributes as
                                        , "optional"
                                        , attributed idlType (tas,t)
                                        , n.value
                                        , defaultV d
                                        ]

export
argumentList : Encoder ArgumentList
argumentList (VarArg args va) =
  sepList' "," (map arg args ++ [vararg va])

argumentList (NoVarArg args optArgs) =
  sepList' "," (map arg args ++ map optArg optArgs)

optArgList : Encoder ArgumentList
optArgList (NoVarArg Nil Nil) = ""
optArgList x                  = inParens argumentList x

--------------------------------------------------------------------------------
--          Members
--------------------------------------------------------------------------------

member : (key : String) -> List String -> String
member "" vs = spaced vs ++ ";"
member k vs  = spaced (k :: vs) ++ ";"

export
const : Encoder Const
const (MkConst t n v) = member "const" [constType t,n.value,"=",constValue v]

export
special : Encoder Special
special Getter  = "getter"
special Setter  = "setter"
special Deleter = "deleter"

export
op : Encoder a -> Encoder (Op a)
op f (MkOp s t n a) =
  member "" [f s, idlType t, maybe "" value n, inParens argumentList a]

export
regularOperation : Encoder RegularOperation
regularOperation = op (const "")

export
specialOperation : Encoder SpecialOperation
specialOperation = op special

export
operation : Encoder Operation
operation = op (maybe "" special)

callbackInterfaceMember : Encoder CallbackInterfaceMember
callbackInterfaceMember = collapseNS . hliftA2 runEnc [const,regularOperation]

callbackInterfaceMembers : Encoder CallbackInterfaceMembers
callbackInterfaceMembers = sepList " " $ attributed callbackInterfaceMember

inheritance : Encoder Inheritance
inheritance = maybe "" $ \i => " : " ++ i.value

dictMemberRest : Encoder DictionaryMemberRest
dictMemberRest (Required as t n) =
  member "required" [attributes as,idlType t,n.value]
dictMemberRest (Optional t n d) =
  member "" [idlType t, n.value, defaultV d]

dictMembers : Encoder DictionaryMembers
dictMembers = sepList " " $ attributed dictMemberRest

readonly : Encoder a -> Encoder (Readonly a)
readonly f = ("readonly " ++) . f . value

inherit : Encoder a -> Encoder (Inherit a)
inherit f = ("inherit " ++) . f . value

attribute : Encoder Attribute
attribute (MkAttribute as t n) =
  member "attribute" [attributes as, idlType t, n.value]

stringifier : Encoder Stringifier
stringifier = ("stringifier " ++)
            . collapseNS
            . hliftA2 runEnc [attribute,readonly attribute,regularOperation,const ";"]

static : Encoder StaticMember
static = ("static " ++)
       . collapseNS
       . hliftA2 runEnc [attribute,readonly attribute,regularOperation]

maplike : Encoder Maplike
maplike (MkMaplike l r) =
  member "maplike" ["<",attributed idlType l,",",attributed idlType r,">"]

setlike : Encoder Setlike
setlike (MkSetlike p) = member "setlike" ["<",attributed idlType p,">"]

namespaceMember : Encoder NamespaceMember
namespaceMember = collapseNS
                . hliftA2 runEnc [regularOperation,readonly attribute]

namespaceMembers : Encoder NamespaceMembers
namespaceMembers = sepList " " $ attributed namespaceMember

constructor_ : Encoder Constructor
constructor_ (MkConstructor args) =
  member "constructor" [inParens argumentList args]

partialInterfaceMember : Encoder PartialInterfaceMember
partialInterfaceMember (IConst x)       = const x
partialInterfaceMember (IOp x)          = operation x
partialInterfaceMember (IAttr x)        = attribute x
partialInterfaceMember (IAttrRO x)      = readonly attribute x
partialInterfaceMember (IAttrInh x)     = inherit attribute x
partialInterfaceMember (IMap x)         = maplike x
partialInterfaceMember (IMapRO x)       = readonly maplike x
partialInterfaceMember (ISet x)         = setlike x
partialInterfaceMember (ISetRO x)       = readonly setlike x
partialInterfaceMember (IStr x)         = stringifier x
partialInterfaceMember (IStatic x)      = static x
partialInterfaceMember (IIterable p o)  =
  member "iterable" ["<",attributed idlType p,optionalType o,">"]
partialInterfaceMember (IAsync p o a)   =
  member "async iterable"
    ["<",attributed idlType p,optionalType o,">",optArgList a]

mixinMember : Encoder MixinMember
mixinMember (MConst x)       = const x
mixinMember (MOp x)          = regularOperation x
mixinMember (MAttr x)        = attribute x
mixinMember (MAttrRO x)      = readonly attribute x
mixinMember (MStr x)         = stringifier x

partialInterfaceMembers : Encoder PartialInterfaceMembers
partialInterfaceMembers = sepList " " $ attributed partialInterfaceMember

mixinMembers : Encoder MixinMembers
mixinMembers = sepList " " $ attributed mixinMember

export
interfaceMember : Encoder InterfaceMember
interfaceMember = collapseNS
                . hliftA2 runEnc [constructor_,partialInterfaceMember]

interfaceMembers : Encoder InterfaceMembers
interfaceMembers = sepList " " $ attributed interfaceMember

--------------------------------------------------------------------------------
--          Definition
--------------------------------------------------------------------------------

def : ExtAttributeList -> (key : String) -> List String -> String
def as ""  ss = attributes as ++ spaced ss ++ ";"
def as key ss = attributes as ++ spaced (key :: ss) ++ ";"

callback : Encoder Callback
callback (MkCallback as n t args) =
  def as "callback" [n.value, "=", idlType t, inParens argumentList args]

callbackInterface : Encoder CallbackInterface
callbackInterface (MkCallbackInterface as n ms) =
  def as "callback interface"
  [n.value, inBraces callbackInterfaceMembers ms]

dictionary : Encoder Dictionary
dictionary (MkDictionary as n i ms) =
  def as "dictionary"
  [n.value, inheritance i, inBraces dictMembers ms]

enum : Encoder Enum
enum (MkEnum as n vs) =
  def as "enum" [n.value, inBraces (sepList "," interpolate) (forget vs)]

iface : Encoder Interface
iface (MkInterface as n i ms) =
  def as "interface" [n.value, inheritance i, inBraces interfaceMembers ms]

includes : Encoder Includes
includes (MkIncludes as a b) = def as "" [a.value,"includes",b.value]

mixin : Encoder Mixin
mixin (MkMixin as n ms) =
  def as "interface mixin" [n.value, inBraces mixinMembers ms]

nspace : Encoder Namespace
nspace (MkNamespace as n ms) =
  def as "namespace" [n.value, inBraces namespaceMembers ms]

pdictionary : Encoder PDictionary
pdictionary (MkPDictionary as n ms) =
  def as "partial dictionary" [n.value, inBraces dictMembers ms]

pinterface : Encoder PInterface
pinterface (MkPInterface as n ms) =
  def as "partial interface" [n.value, inBraces partialInterfaceMembers ms]

pmixin : Encoder PMixin
pmixin (MkPMixin as n ms) =
  def as "partial interface mixin" [n.value, inBraces mixinMembers ms]

pnamespace : Encoder PNamespace
pnamespace (MkPNamespace as n ms) =
  def as "partial namespace" [n.value, inBraces namespaceMembers ms]

typedef : Encoder Typedef
typedef (MkTypedef as tas t n) =
  def as "typedef" [attributes tas, idlType t, n.value]

export
definition : Encoder Definition
definition = collapseNS
           . hliftA2 runEnc [ callback
                            , callbackInterface
                            , dictionary
                            , enum
                            , includes
                            , iface
                            , mixin
                            , nspace
                            , typedef
                            ]

export
part : Encoder Part
part = collapseNS . hliftA2 runEnc [pdictionary,pinterface,pmixin,pnamespace]

export
partOrDef : Encoder PartOrDef
partOrDef (Z p) = part p
partOrDef (S $ Z d) = definition d
