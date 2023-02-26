module Text.WebIDL.Parser.Type

import Text.WebIDL.Parser.Util

%default total

int : Rule True IntType
int (B "long" _ :: B "long" _ :: xs) = Succ0 LongLong xs
int (B "long" _ :: xs)               = Succ0 Long xs
int (B "short" _ :: xs)              = Succ0 Short xs
int xs                               = fail xs

float : Rule True FloatType
float (B "double" _ :: xs) = Succ0 Dbl xs
float (B "float" _ :: xs)  = Succ0 Float xs
float xs                   = fail xs

primitive : Rule True PrimitiveType
primitive (B "boolean" _ :: xs)      = Succ0 Boolean xs
primitive (B "byte" _ :: xs)         = Succ0 Byte xs
primitive (B "octet" _ :: xs)        = Succ0 Octet xs
primitive (B "bigint" _ :: xs)       = Succ0 BigInt xs
primitive (B "undefined" _ :: xs)    = Succ0 Undefined xs
primitive (B "unsigned" _ :: xs)     = succT $ Unsigned <$> int xs
primitive (B "unrestricted" _ :: xs) = succT $ Unrestricted <$> float xs
primitive xs = map Signed (int xs) <|> map Restricted (float xs)

simple : Rule True Distinguishable
simple (B "ArrayBuffer" _ :: xs)       = Succ0 (B ArrayBuffer) xs
simple (B "DataView"  _ :: xs)         = Succ0 (B DataView) xs
simple (B "Int8Array" _ :: xs)         = Succ0 (B Int8Array) xs
simple (B "Int16Array" _ :: xs)        = Succ0 (B Int16Array) xs
simple (B "Int32Array" _ :: xs)        = Succ0 (B Int32Array) xs
simple (B "Uint8Array" _ :: xs)        = Succ0 (B Uint8Array) xs
simple (B "Uint16Array" _ :: xs)       = Succ0 (B Uint16Array) xs
simple (B "Uint32Array" _ :: xs)       = Succ0 (B Uint32Array) xs
simple (B "Uint8ClampedArray" _ :: xs) = Succ0 (B Uint8ClampedArray) xs
simple (B "Float32Array" _ :: xs)      = Succ0 (B Float32Array) xs
simple (B "Float64Array" _ :: xs)      = Succ0 (B Float64Array) xs
simple (B "ByteString" _ :: xs)        = Succ0 (S ByteString) xs
simple (B "DOMString" _ :: xs)         = Succ0 (S DOMString) xs
simple (B "USVString" _ :: xs)         = Succ0 (S USVString) xs
simple xs                              = P <$> primitive xs

constType : Rule True ConstType
constType (B (Ident i) _ :: xs) = Succ0 (CI i) xs
constType xs                    = CP <$> primitive xs

-- nullable : IdlGrammar a -> IdlGrammar (Nullable a)
-- nullable g = map MaybeNull (g <* symbol '?') <|> map NotNull g

distinguishable : AccRule True IdlType

-- Type ::
--     SingleType
--     UnionType Null
--
-- SingleType ::
--     DistinguishableType
--     any
--     PromiseType
-- PromiseType ::
--     Promise < Type >
export
idlType : AccRule True IdlType
idlType (B "any" _ :: xs) _ = Succ0 Any xs
idlType (B "Promise" _ :: B '<' b :: xs) (SA r) = case succT $ idlType xs r of
  Succ0 t (B '>' _ :: ys) => Succ0 (Promise t) ys
  xs                      => failInParen b '<' xs
idlType xs acc = distinguishable xs acc

-- 
-- mutual
--   export
--   idlType =   (key "any" $> Any)
--           <|> map Promise (key "Promise" *> inAngles idlType)
--           <|> map D distinguishableType
--           <|> (nullable flatUnion >>= map U . fromFlatUnion)
-- 
--     where um : Attributed (Nullable Distinguishable) -> UnionMemberType
--           um (a, MaybeNull x) = MkUnionMember a x
--           um (a, NotNull x)   = MkUnionMember a x
-- 
--           fromFlatUnion :  Nullable (List1 $ Attributed $ Nullable Distinguishable)
--                         -> IdlGrammar' (Nullable UnionType)
--           fromFlatUnion (MaybeNull $ a ::: b :: t) =
--             pure . MaybeNull $ UT (um a) (um b) (map um t)
-- 
--           fromFlatUnion (NotNull   $ a ::: b :: t) =
--             if any (isNullable . snd) (a::b::t)
--                then pure . MaybeNull $ UT (um a) (um b) (map um t)
--                else pure . NotNull   $ UT (um a) (um b) (map um t)
-- 
--           fromFlatUnion _                          = fail "no enough union members"

--   -- TypeWithExtendedAttributes ::
--   --     ExtendedAttributeList Type
--   attrTpe : IdlGrammar (Attributed IdlType)
--   attrTpe = attributed idlType
-- 
--   -- RecordType ::
--   --     record < StringType , TypeWithExtendedAttributes >
--   recrd : IdlGrammar Distinguishable
--   recrd = Record <$> (key "record" *> symbol '<' *> stringType)
--                  <*> (comma *> attributes)
--                  <*> (idlType <* symbol '>')
-- 
--   -- DistinguishableType ::
--   --     PrimitiveType Null
--   --     StringType Null
--   --     identifier Null
--   --     sequence < TypeWithExtendedAttributes > Null
--   --     object Null
--   --     symbol Null
--   --     BufferRelatedType Null
--   --     FrozenArray < TypeWithExtendedAttributes > Null
--   --     ObservableArray < TypeWithExtendedAttributes > Null
--   --     RecordType Null
--   distinguishable : IdlGrammar Distinguishable
--   distinguishable =
--         map P primitive
--     <|> map S stringType
--     <|> map B bufferRelated
--     <|> (key "object" $> Object)
--     <|> (key "symbol" $> Symbol)
--     <|> (key "sequence" *> inAngles [| Sequence attributes idlType |])
--     <|> (key "FrozenArray" *> inAngles [| FrozenArray attributes idlType |])
--     <|> (key "ObservableArray" *> inAngles [| ObservableArray attributes idlType |])
--     <|> recrd
--     <|> map I ident
-- 
--   distinguishableType : IdlGrammar (Nullable Distinguishable)
--   distinguishableType = nullable distinguishable
-- 
--   -- UnionType ::
--   --     ( UnionMemberType or UnionMemberType UnionMemberTypes )
--   --
--   -- UnionMemberTypes ::
--   --     or UnionMemberType UnionMemberTypes
--   --     ε
--   flatUnion : IdlGrammar (List1 $ Attributed $ Nullable Distinguishable)
--   flatUnion = inParens $ do (a :: b :: t) <- sepBy (key "or") flatMember
--                               | _ => fail "Non enough Union members"
--                             pure (join $ a ::: b :: t)
-- 
--   -- UnionMemberType ::
--   --     ExtendedAttributeList DistinguishableType
--   --     UnionType Null
--   flatMember : IdlGrammar (List1 $ Attributed $ Nullable Distinguishable)
--   flatMember = map singleton (attributed distinguishableType) <|> flatUnion
-- 
-- optionalType : IdlGrammar' OptionalType
-- optionalType = optional (symbol ',' *> attributed idlType)
