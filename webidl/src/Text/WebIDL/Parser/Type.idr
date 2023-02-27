module Text.WebIDL.Parser.Type

import Text.WebIDL.Parser.Attributes
import Text.WebIDL.Parser.Util

%default total

data UnionTree : Bool -> Type where
  Leaf   : UnionMemberType -> UnionTree False
  Branch : UnionTree b -> UnionTree c -> UnionTree d

weaken : UnionTree x -> UnionTree False
weaken (Leaf m)     = Leaf m
weaken (Branch l r) = Branch l r

flat : UnionTree b -> List1 UnionMemberType
flat (Leaf x)     = singleton x
flat (Branch x y) = flat x ++ flat y

flatten : Nullable (UnionTree True) -> IdlType
flatten x =
  let Branch l r  := val x
      (hl ::: tl) := flat l
      (hr ::: tr) := flat r
   in case tl of
        []     => U $ x $> UT hl hr tr
        (h::t) => U $ x $> UT hl h  (t ++ hr :: tr)

int : Rule True IntType
int (B "long" _ :: B "long" _ :: xs) = Succ0 LongLong xs
int (B "long" _ :: xs)               = Succ0 Long xs
int (B "short" _ :: xs)              = Succ0 Short xs
int xs                               = fail xs

float : Rule True FloatType
float (B "double" _ :: xs) = Succ0 Dbl xs
float (B "float" _ :: xs)  = Succ0 Float xs
float xs                   = fail xs

export
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

export
constType : Rule True ConstType
constType (B (Ident i) _ :: xs) = Succ0 (CI i) xs
constType xs                    = CP <$> primitive xs

idlAttr : (ExtAttributeList -> IdlType -> a) -> AccRule True a

idlAttrAngle : (ExtAttributeList -> IdlType -> a) -> AccRule True a

idlTpe : AccRule True IdlType

unionMember : AccRule True (Nullable $ UnionTree False)

unionRest : Bounds -> AccRule True (Nullable $ UnionTree False)

union : Bounds -> AccRule True (Nullable $ UnionTree True)

-- RecordType ::
--     record < StringType , TypeWithExtendedAttributes >
recrd : Bounds -> StringType -> AccRule True Distinguishable
recrd b s (B ',' _ :: xs) (SA r) = case succT (idlAttr (Record s) xs r) of
  Succ0 t (B '>' _ :: ys) => Succ0 t ys
  res                     => failInParen b '<' res
recrd b s (x :: xs) _ = expected x.bounds ','
recrd b s []        _ = eoi

  -- DistinguishableType ::
  --     PrimitiveType Null
  --     StringType Null
  --     identifier Null
  --     sequence < TypeWithExtendedAttributes > Null
  --     object Null
  --     symbol Null
  --     BufferRelatedType Null
  --     FrozenArray < TypeWithExtendedAttributes > Null
  --     ObservableArray < TypeWithExtendedAttributes > Null
  --     RecordType Null
distinguishable : AccRule True Distinguishable
distinguishable [] _           = eoi
distinguishable (x::xs) (SA r) = case x.val of
  "object"          => Succ0 Object xs
  "symbol"          => Succ0 Symbol xs
  "sequence"        => succT (idlAttrAngle Sequence xs r)
  "FrozenArray"     => succT (idlAttrAngle FrozenArray xs r)
  "ObservableArray" => succT (idlAttrAngle ObservableArray xs r)
  "record"          => case xs of
    B '<' b :: B "DOMString"  _ :: ys => succT (recrd b DOMString ys r)
    B '<' b :: B "ByteString" _ :: ys => succT (recrd b ByteString ys r)
    B '<' b :: B "USVString"  _ :: ys => succT (recrd b USVString ys r)
    B '<' b :: y :: ys  => unexpected y
    B '<' b :: []       => unclosed b '<'
    x :: xs             => expected x.bounds '<'
    []                  => eoi
  Ident i           => Succ0 (I i) xs
  _                 => simple (x::xs)

distinguishableType : AccRule True (Nullable Distinguishable)
distinguishableType ts acc = case distinguishable ts acc of
  Succ0 d (B '?' _ :: xs) => Succ0 (MaybeNull d) xs
  Succ0 d xs              => Succ0 (NotNull d) xs
  Fail0 err               => Fail0 err

unionMember (B '(' b :: xs) (SA r) = succT (map weaken <$> union b xs r)
unionMember (B '[' b :: xs) (SA r) =
  let Succ0 as r1 := succT $ eas [<] b xs r | Fail0 err => Fail0 err
   in map (Leaf . MkUnionMember as) <$> succT (distinguishableType r1 r)
unionMember xs a = map (Leaf . MkUnionMember []) <$> distinguishableType xs a

union b xs acc@(SA r) = case unionMember xs acc of
  Succ0 u1 (B "or" _ :: ys) => succT (zipWith Branch u1 <$> unionRest b ys r)
  Succ0 _  (x :: _)         => expected x.bounds "or"
  res                       => failInParen b '(' res

unionRest b xs acc@(SA r) = case unionMember xs acc of
  Succ0 u1 (B "or" _ :: ys) => succT (zipWith Branch u1 <$> unionRest b ys r)
  Succ0 u1 (B ')' _  :: B '?' _ :: ys) => Succ0 (MaybeNull $ val u1) ys
  Succ0 u1 (B ')' _  :: ys) => Succ0 u1 ys
  res                       => failInParen b '(' res

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
idlTpe (B "any" _ :: xs) _ = Succ0 Any xs
idlTpe (B "Promise" _ :: B '<' b :: xs) (SA r) = case succT $ idlTpe xs r of
  Succ0 t (B '>' _ :: ys) => Succ0 (Promise t) ys
  xs                      => failInParen b '<' xs
idlTpe (B '(' b :: xs) (SA r)  = flatten <$> succT (union b xs r)
idlTpe xs acc = D <$> distinguishableType xs acc

idlAttr f (B '[' b :: xs) (SA r) = case succT (eas [<] b xs r) of
  Succ0 as ys => f as <$> succT (idlTpe ys r)
  Fail0 err   => Fail0 err
idlAttr f xs acc = f [] <$> idlTpe xs acc

idlAttrAngle f (B '<' b :: xs) (SA r) = case succT (idlAttr f xs r) of
  Succ0 v (B '>' _ :: ys) => Succ0 v ys
  res                     => failInParen b '<' res
idlAttrAngle f (x::xs) _ = expected x.bounds '<'
idlAttrAngle f []      _ = eoi

export %inline
idlType : Rule True IdlType
idlType = acc idlTpe

export %inline
optionalType : Rule False OptionalType
optionalType (B ',' _ :: xs) = succF $ Just <$> attributed idlType xs
optionalType xs              = Succ0 Nothing xs
