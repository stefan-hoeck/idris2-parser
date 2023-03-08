module Text.WebIDL.Parser.Definitions

import Text.Parse.Syntax
import Text.WebIDL.Parser.Arguments
import Text.WebIDL.Parser.Attributes
import Text.WebIDL.Parser.Members
import Text.WebIDL.Parser.Type
import Text.WebIDL.Parser.Util

%default total

%hide Prelude.(<*>)
%hide Prelude.(*>)
%hide Prelude.(<*)
%hide Prelude.pure

%default total

inherits : Rule False Inheritance
inherits (B ':' _ :: B (Ident i) _ :: xs) = Succ0 (Just i) xs
inherits xs                               = Succ0 Nothing xs

def :
     {0 ts : List Type}
  -> Rule True a
  -> {auto p : Elem a ts}
  -> Rule True (NS I ts)
def f xs = inj $ (f <* exact ';') xs

-- optional trailing comma
enumRest: Bounds -> SnocList StringLit -> Rule False (List StringLit)
enumRest b ss (B ',' _ :: B '}' _ :: xs)      = Succ0 (ss <>> []) xs
enumRest b ss (B ',' _ :: B (SLit s) _ :: xs) = succF $ enumRest b (ss :< s) xs
enumRest b ss (B ',' _ :: x  :: xs)           = custom x.bounds ExpectedStringLit
enumRest b ss (B '}' _ :: xs)                 = Succ0 (ss <>> []) xs
enumRest b ss (x :: xs)                       = expected x.bounds ','
enumRest b ss []                              = unclosed b '{'

-- optional trailing comma
enumList : Rule True (List1 StringLit)
enumList (B '{' b :: B (SLit s) _ :: xs) = (s :::) <$> succT (enumRest b [<] xs)
enumList (B '{' b :: x :: xs) = custom x.bounds ExpectedStringLit               
enumList (x :: xs)            = expected x.bounds '{'
enumList []                   = eoi

defn : Rule False ExtAttributeList -> Rule True Definition
defn as (B "enum" _ :: xs) = 
  succT $ def [| MkEnum as ident enumList |] xs
defn as (B "typedef" _ :: xs) = 
  succT $ def [| MkTypedef as attributes idlType ident |] xs
defn as (B "namespace" _ :: xs) = 
  succT $ def [| MkNamespace as ident (members namespaceM) |] xs
defn as (B "interface" _ :: B "mixin" _ :: xs) = 
  succT $ def [| MkMixin as ident (members mixinM) |] xs
defn as (B "interface" _ :: xs) = 
  succT $ def [| MkInterface as ident inherits (members ifaceM) |] xs
defn as (B "dictionary" _ :: xs) = 
  succT $ def [| MkDictionary as ident inherits (members dictM) |] xs
defn as (B "callback" _ :: B "interface" _ :: xs) = 
  succT $ def [| MkCallbackInterface as ident (members cbIfaceM) |] xs
defn as (B "callback" _ :: xs) = 
  succT $ def [| MkCallback as ident (exact '=' *> idlType) argumentList |] xs
defn as xs =
  def [| MkIncludes as ident (exact "includes" *> ident) |] xs

prt : Rule False ExtAttributeList -> Rule True Part
prt as (B "namespace" _ :: xs) = 
  succT $ def [| MkPNamespace as ident (members namespaceM) |] xs
prt as (B "interface" _ :: B "mixin" _ :: xs) = 
  succT $ def [| MkPMixin as ident (members mixinM) |] xs
prt as (B "interface" _ :: xs) = 
  succT $ def [| MkPInterface as ident (members pIfaceM) |] xs
prt as (B "dictionary" _ :: xs) = 
  succT $ def [| MkPDictionary as ident (members dictM) |] xs
prt as xs = fail xs

export
partOrDef : Rule True PartOrDef
partOrDef xs = case attributes xs of
  Succ0 as (B "partial" _ :: ys) => succT (inj $ prt (pure as) ys)
  Succ0 as ys @{p}               => trans (inj $ defn (pure as) ys) p
  Fail0 err => Fail0 err

export
partsAndDefs : Rule True PartsAndDefs
partsAndDefs xs = accumNs . forget <$> some partOrDef xs
