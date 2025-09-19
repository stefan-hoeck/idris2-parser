module Text.WebIDL.Parser.Members

import Text.Parse.Syntax
import Text.WebIDL.Parser.Arguments
import Text.WebIDL.Parser.Attributes
import Text.WebIDL.Parser.Type
import Text.WebIDL.Parser.Util

%default total

%hide Prelude.(<*>)
%hide Prelude.(*>)
%hide Prelude.(<*)
%hide Prelude.pure

--------------------------------------------------------------------------------
--          Member
--------------------------------------------------------------------------------

const : Rule True Const
const = [| MkConst constType ident (exact '=' *> constValue) |]

opName : Rule False (Maybe OperationName)
opName  (B "includes" _ :: xs) = Succ0 (Just $ MkOpName "includes") xs
opName  (B (Ident i) _ :: xs)  = Succ0 (Just $ MkOpName i.value) xs
opName  xs                     = Succ0 Nothing xs

regularOperation : Rule True RegularOperation
regularOperation =
  [| MkOp (pure ()) idlType opName argumentList |]

specialOperation : Special -> Rule True Operation
specialOperation s =
  [| MkOp (pure $ Just s) idlType opName argumentList |]

export
operation : Rule True Operation
operation (B "getter" _ :: xs)  = succT $ specialOperation Getter xs
operation (B "setter" _ :: xs)  = succT $ specialOperation Setter xs
operation (B "deleter" _ :: xs) = succT $ specialOperation Deleter xs
operation xs                    = regToOp <$> regularOperation xs

-- callbackInterfaceMemeber
export
cbIfaceM : Rule True CallbackInterfaceMember
cbIfaceM (B "const" _ :: xs ) =  inj (succT $ const xs)
cbIfaceM xs                   =  inj $ regularOperation xs

export
dictM : Rule True DictionaryMemberRest
dictM (B "required" _ :: xs) =
  succT ([| Required attributes idlType ident |] xs)
dictM xs                     =
  [| Optional idlType ident defaultV |] xs

attributeName : Rule True AttributeName
attributeName = terminal $ \case
  Key s   => MkAttributeName . value <$> refineAttributeNameKeyword s.value
  Ident s => Just (MkAttributeName s.value)
  _       => Nothing

attribute : Rule True Attribute
attribute = [| MkAttribute attributes idlType attributeName |]

stringifier : Rule True Stringifier
stringifier (B "attribute" _ :: xs) = succT (inj $ attribute xs)
stringifier (B "readonly" _ :: B "attribute" _ :: xs) =
  succT (inj $ MkRO <$> attribute xs)
stringifier xs = inj $ regularOperation xs

static : Rule True StaticMember
static (B "attribute" _ :: xs) = succT (inj $ attribute xs)
static (B "readonly" _ :: B "attribute" _ :: xs) =
  succT (inj $ MkRO <$> attribute xs)
static xs = inj $ regularOperation xs

maplike : Rule True Maplike
maplike = between '<' '>'
  [| MkMaplike (attributed idlType) (exact ',' *> attributed idlType) |]

setlike : Rule True Setlike
setlike = between '<' '>' [| MkSetlike (attributed idlType) |]

export
namespaceM : Rule True NamespaceMember
namespaceM (B "readonly" _ :: B t b :: xs) = case t of
  "attribute" => inj $ succT (MkRO <$> attribute xs)
  _           => expected b "attribute" "\{t}"
namespaceM xs = inj $ regularOperation xs

iterable : Rule True PartialInterfaceMember
iterable = between '<' '>' [| IIterable (attributed idlType) optionalType|]

async : Rule True PartialInterfaceMember
async = [| IAsync (attributed idlType) (optionalType <* exact '>') optArgList |]

export
pIfaceM : Rule True PartialInterfaceMember
pIfaceM (B "const" _     :: xs) = IConst <$> succT (const xs)
pIfaceM (B "attribute" _ :: xs) = IAttr <$> succT (attribute xs)
pIfaceM (B "readonly" _ :: B t b :: xs) = case t of
  "maplike"   => IMapRO . MkRO <$> succT (maplike xs)
  "setlike"   => ISetRO . MkRO <$> succT (setlike xs)
  "attribute" => IAttrRO . MkRO <$> succT (attribute xs)
  _          => unexpected (B t b)
pIfaceM (B "inherit" _ :: B "attribute" _ :: xs) =
  IAttrInh . MkI <$> succT (attribute xs)
pIfaceM (B "maplike" _ :: xs) = IMap <$> succT (maplike xs)
pIfaceM (B "setlike" _ :: xs) = ISet <$> succT (setlike xs)
pIfaceM (B "stringifier" _ :: xs) = case xs of
  B ';' b :: ys => Succ0 (IStr $ inject ()) (B (Other $ Symb ';') b :: ys)
  _             => IStr <$> succT (stringifier xs)
pIfaceM (B "static" _ :: xs) = IStatic <$> succT (static xs)
pIfaceM (B "iterable" _ :: xs) = succT $ iterable xs
pIfaceM (B "async" _ :: B "iterable" _ :: B '<' _ :: xs) = succT $ async xs
pIfaceM xs = IOp <$> operation xs

export
mixinM : Rule True MixinMember
mixinM (B "const" _     :: xs) = MConst <$> succT (const xs)
mixinM (B "attribute" _ :: xs) = MAttr <$> succT (attribute xs)
mixinM (B "readonly" _ :: B t b :: xs) = case t of
  "attribute" => MAttrRO . MkRO <$> succT (attribute xs)
  _           => expected b "attribute" "\{t}"
mixinM (B "stringifier" _ :: xs) = case xs of
  B ';' b :: ys => Succ0 (MStr $ inject ()) (B (Other $ Symb ';') b :: ys)
  _             => MStr <$> succT (stringifier xs)
mixinM xs = MOp <$> regularOperation xs

export
ifaceM : Rule True InterfaceMember
ifaceM (B "constructor" _ :: xs) =
  succT $ inj (MkConstructor <$> argumentList xs)
ifaceM xs = inj $ pIfaceM xs

mems :
     SnocList (Attributed a)
  -> Bounds
  -> Rule True a
  -> AccRule True (List $ Attributed a)
mems sx b f ts (SA r) = case attributed f ts of
  Succ0 p (B ';' _ :: B '}' _ :: ys) => Succ0 (sx <>> [p]) ys
  Succ0 p (B ';' _ :: ys)            => succT $ mems (sx :< p) b f ys r
  Succ0 p (x::xs)                    => expected x.bounds ";" "\{x.val}"
  res                                => failInParen b '{' res

export
members : Rule True a -> Rule True (List $ Attributed a)
members g (B '{' _ :: B '}' _ :: xs) = Succ0 [] xs
members g (B '{' b :: xs) = succT $ acc (mems [<] b g) xs
members g (x::xs) = expected x.bounds "{" "\{x.val}"
members g [] = eoi
