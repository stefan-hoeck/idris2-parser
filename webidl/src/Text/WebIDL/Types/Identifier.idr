module Text.WebIDL.Types.Identifier

import Data.List1
import Data.Refined
import Derive.Prelude
import Derive.Refined

%default total
%language ElabReflection

%default total

%language ElabReflection

--------------------------------------------------------------------------------
--          Keyword Predicates
--------------------------------------------------------------------------------

||| Checks, whether a given string corresponds to a WebIDL
||| argument name keyword.
public export
IsArgumentNameKeyword : String -> Bool
IsArgumentNameKeyword "async"        = True
IsArgumentNameKeyword "attribute"    = True
IsArgumentNameKeyword "callback"     = True
IsArgumentNameKeyword "const"        = True
IsArgumentNameKeyword "constructor"  = True
IsArgumentNameKeyword "deleter"      = True
IsArgumentNameKeyword "dictionary"   = True
IsArgumentNameKeyword "enum"         = True
IsArgumentNameKeyword "getter"       = True
IsArgumentNameKeyword "includes"     = True
IsArgumentNameKeyword "inherit"      = True
IsArgumentNameKeyword "interface"    = True
IsArgumentNameKeyword "iterable"     = True
IsArgumentNameKeyword "maplike"      = True
IsArgumentNameKeyword "mixin"        = True
IsArgumentNameKeyword "namespace"    = True
IsArgumentNameKeyword "partial"      = True
IsArgumentNameKeyword "readonly"     = True
IsArgumentNameKeyword "required"     = True
IsArgumentNameKeyword "setlike"      = True
IsArgumentNameKeyword "setter"       = True
IsArgumentNameKeyword "static"       = True
IsArgumentNameKeyword "stringifier"  = True
IsArgumentNameKeyword "typedef"      = True
IsArgumentNameKeyword "unrestricted" = True
IsArgumentNameKeyword _              = False

IsAttributeNameKeyword : String -> Bool
IsAttributeNameKeyword "async"    = True
IsAttributeNameKeyword "required" = True
IsAttributeNameKeyword _          = False

||| Checks, whether a given string corresponds to one
||| of the floating point constants "NaN", "Infinity", or
||| "-Infinity".
public export
IsFloatKeyword : String -> Bool
IsFloatKeyword "NaN"       = True
IsFloatKeyword "Infinity"  = True
IsFloatKeyword "-Infinity" = True
IsFloatKeyword _           = False

||| Checks, whether a given string corresponds to any WebIDL keyword.
public export
IsKeyword : String -> Bool
IsKeyword "ArrayBuffer"       = True
IsKeyword "ByteString"        = True
IsKeyword "DOMString"         = True
IsKeyword "DataView"          = True
IsKeyword "Float32Array"      = True
IsKeyword "Float64Array"      = True
IsKeyword "FrozenArray"       = True
IsKeyword "Int16Array"        = True
IsKeyword "Int32Array"        = True
IsKeyword "Int8Array"         = True
IsKeyword "ObservableArray"   = True
IsKeyword "Promise"           = True
IsKeyword "USVString"         = True
IsKeyword "Uint16Array"       = True
IsKeyword "Uint32Array"       = True
IsKeyword "Uint8Array"        = True
IsKeyword "Uint8ClampedArray" = True
IsKeyword "any"               = True
IsKeyword "bigint"            = True
IsKeyword "boolean"           = True
IsKeyword "byte"              = True
IsKeyword "double"            = True
IsKeyword "false"             = True
IsKeyword "float"             = True
IsKeyword "long"              = True
IsKeyword "null"              = True
IsKeyword "object"            = True
IsKeyword "octet"             = True
IsKeyword "optional"          = True
IsKeyword "or"                = True
IsKeyword "record"            = True
IsKeyword "sequence"          = True
IsKeyword "short"             = True
IsKeyword "symbol"            = True
IsKeyword "true"              = True
IsKeyword "undefined"         = True
IsKeyword "unsigned"          = True
IsKeyword s = IsArgumentNameKeyword s || IsFloatKeyword s

--------------------------------------------------------------------------------
--          Keyword
--------------------------------------------------------------------------------

public export
record Keyword where
  constructor MkKeyword
  value : String
  0 isValid : Holds IsKeyword value

export %inline
Interpolation Keyword where interpolate = value

namespace Keyword
  %runElab derive "Keyword" [Show,Eq,Ord,RefinedString]

--------------------------------------------------------------------------------
--          ArgumentNameKeyword
--------------------------------------------------------------------------------

public export
record ArgumentNameKeyword where
  constructor MkArgumentNameKeyword
  value : String
  0 isValid : Holds IsArgumentNameKeyword value

export %inline
Interpolation ArgumentNameKeyword where interpolate = value

namespace ArgumentNameKeyword
  %runElab derive "ArgumentNameKeyword" [Show,Eq,Ord,RefinedString]

--------------------------------------------------------------------------------
--          AttributeNameKeyword
--------------------------------------------------------------------------------

||| Wrapper for one of the attribute name keywords
public export
record AttributeNameKeyword where
  constructor MkAttributeNameKeyword
  value : String
  0 isValid : Holds IsAttributeNameKeyword value

export %inline
Interpolation AttributeNameKeyword where interpolate = value

namespace AttributeNameKeyword
  %runElab derive "AttributeNameKeyword" [Show,Eq,Ord,RefinedString]

--------------------------------------------------------------------------------
--          Identifier
--------------------------------------------------------------------------------

||| Identifier
public export
record Identifier where
  constructor MkIdent
  value : String

export %inline
Interpolation Identifier where interpolate = value

%runElab derive "Identifier" [Eq,Ord,Show,FromString]

||| IdentifierList :: identifier Identifiers
||| Identifiers :: "," identifier Identifiers | ε
public export
0 IdentifierList : Type
IdentifierList = List1 Identifier

--------------------------------------------------------------------------------
--          Idris Identifier
--------------------------------------------------------------------------------

||| Checks, if a String corresponds to an Idris2 keyword.
public export
IsIdrisKeyword : String -> Bool
IsIdrisKeyword "covering"       = True
IsIdrisKeyword "data"           = True
IsIdrisKeyword "do"             = True
IsIdrisKeyword "default"        = True
IsIdrisKeyword "else"           = True
IsIdrisKeyword "export"         = True
IsIdrisKeyword "if"             = True
IsIdrisKeyword "implementation" = True
IsIdrisKeyword "interface"      = True
IsIdrisKeyword "module"         = True
IsIdrisKeyword "mutual"         = True
IsIdrisKeyword "namespace"      = True
IsIdrisKeyword "open"           = True
IsIdrisKeyword "parameters"     = True
IsIdrisKeyword "partial"        = True
IsIdrisKeyword "private"        = True
IsIdrisKeyword "prefix"         = True
IsIdrisKeyword "public"         = True
IsIdrisKeyword "record"         = True
IsIdrisKeyword "then"           = True
IsIdrisKeyword "total"          = True
IsIdrisKeyword "using"          = True
IsIdrisKeyword "where"          = True
IsIdrisKeyword _                = False

||| Wrapper type making sure that no Idris2 keyword
||| is used as a function's name
public export
data IdrisIdent : Type where
  ||| A string that was successfully checked to be not
  ||| an Idris2 keyword. This can be used without further
  ||| adjustments as an Idris2 identifier.
  II :
       (v : String)
    -> {auto 0 _ : Holds (Prelude.not . IsIdrisKeyword) v}
    -> IdrisIdent

  ||| Primitive function name. This will be prefixed by
  ||| "prim__" during code generation. As such, the resulting
  ||| identifier always valid in idris.
  Prim : (v : String) -> IdrisIdent

  ||| Fallback constructor for Idris2 keywords. An underscore
  ||| will be appended to the wrapped string during code generation.
  Underscore : (v : String) -> IdrisIdent

%runElab derive "IdrisIdent" [Eq,Show]

public export
Interpolation IdrisIdent where
  interpolate (II v) =  case strM  v of
    StrCons '_' xs => xs
    _              => v
  interpolate (Prim v) = "prim__\{v}"
  interpolate (Underscore v) = "\{v}_"

public export
FromString IdrisIdent where
  fromString s = case hdec0 {p = Holds (not . IsIdrisKeyword)} s of
    Nothing0 => Underscore s
    Just0 _  => II s

export %inline
fromIdent : Identifier -> IdrisIdent
fromIdent = fromString . value
