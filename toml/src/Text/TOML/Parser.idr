module Text.TOML.Parser

import Data.List1
import Data.SortedMap
import Text.Parse.Manual
import Text.Parse.Syntax
import Text.TOML.Lexer
import Text.TOML.Types

%default total

public export
data ElemType : Type where
  Table : TableType -> ElemType
  Array : ArrayType -> ElemType

public export
0 ParentType : ElemType -> Type
ParentType (Table _) = TomlTable
ParentType (Array _) = SnocList TomlValue

||| Key together with the a value and its type encountered in a
||| TOML tree.
public export
record PathElem where
  constructor PE
  tpe    : ElemType
  parent : ParentType tpe
  key    : KeyToken

public export
record TOMLView where
  constructor TV
  path : SnocList PathElem
  cur  : Maybe TomlValue

keyErr :
     SnocList PathElem
  -> (List KeyToken -> TomlParseError)
  -> Either (Bounded TomlErr) a
keyErr sx f =
  let ks := map key (sx <>> [])
   in Left (B (Custom $ f ks) $ concatMap bounds ks)

public export
pth :
     SnocList PathElem
  -> List KeyToken
  -> Maybe TomlValue
  -> Either (Bounded TomlErr) TOMLView 
pth sx []        m = Right $ TV sx m
pth sx (x :: xs) m = case m of
  Nothing                 => pth (sx :< PE (Table None) empty x) xs Nothing
  Just (TTbl Inline _)    => keyErr sx InlineTableExists
  Just (TTbl tag t)       => pth (sx :< PE (Table tag) t x) xs (lookup x.key t)
  Just (TArr Static _)    => keyErr sx StaticArray
  Just (TArr tag sv)     => case sv of
    [<] => pth (sx :< PE (Array tag) [<TTbl None empty] x) xs Nothing
    (_ :< TTbl Inline _)  => keyErr sx InlineTableExists
    (_ :< TTbl tg t)      => pth (sx :< PE (Array tag) sv x) xs (lookup x.key t)
    _                     => keyErr sx ValueExists
  Just v                  => keyErr sx ValueExists

%inline
path : List KeyToken -> (root : TomlValue) -> Either (Bounded TomlErr) TOMLView
path xs root = pth [<] xs (Just root)

ins : SnocList PathElem -> TomlValue -> TomlValue
ins [<]                      v = v
ins (sx :< PE (Table x) t  k) v = ins sx (TTbl x $ insert k.key v t)
ins (sx :< PE (Array x) sv k) v = case sv of
  sy :< TTbl tag t => ins sx (TArr x $ sy :< (TTbl tag $ insert k.key v t))
  _                => ins sx (TArr x sv)

append : SnocList PathElem -> SnocList TomlValue -> TomlValue -> TomlValue
append p sx = ins p . TArr OfTables . (sx :<)

public export
tableAt :
     List1 KeyToken
  -> (root : TomlValue)
  -> Either (Bounded TomlErr) (SnocList PathElem, TomlValue)
tableAt xs root = case path (forget xs) root of
  Left err => Left err
  Right (TV path Nothing)                => Right (path, TTbl Table empty)
  Right (TV path (Just $ TTbl None t))   => Right (path, TTbl Table t)
  Right (TV path (Just $ TTbl Inline t)) => keyErr path InlineTableExists
  Right (TV path (Just $ TTbl Table t))  => keyErr path TableExists
  Right (TV path (Just x))               => keyErr path ValueExists

public export
arrayAt :
     List1 KeyToken
  -> (root : TomlValue)
  -> Either (Bounded TomlErr) (SnocList PathElem, SnocList TomlValue)
arrayAt xs root = case path (forget xs) root of
  Left err => Left err
  Right (TV path Nothing)                   => Right (path, [<])
  Right (TV path (Just $ TTbl _ t))         => keyErr path TableExists
  Right (TV path (Just $ TArr Static t))    => keyErr path StaticArray
  Right (TV path (Just $ TArr OfTables sv)) => Right (path, sv)
  Right (TV path (Just x))                  => keyErr path ValueExists

public export
tryInsert :
     List1 KeyToken
  -> (val,root : TomlValue)
  -> Either (Bounded TomlErr) TomlValue
tryInsert x val root = case path (forget x) root of
  Left y                  => Left y
  Right (TV path Nothing) => Right $ ins path val
  Right (TV path _)       => keyErr path ValueExists

public export
data TomlItem : Type where
  TableName : List1 KeyToken -> TomlItem
  ArrayName : List1 KeyToken -> TomlItem
  KeyVal    : List1 KeyToken -> TomlValue -> TomlItem

toTable : TomlValue -> TomlItem -> AccumRes TomlValue (Bounded TomlErr)
toTable root (KeyVal k v) = either Error Cont $ tryInsert k v root
toTable _    _            = Done

assemble :
     (top   : TomlValue)
  -> (items : List TomlItem)
  -> (0 acc : SuffixAcc items)
  -> Either (Bounded TomlErr) TomlValue
assemble top (x :: xs) (SA r) = case x of
  KeyVal k v =>
   let Right t1    := tryInsert k v top | Left err => Left err
       Succ0 t2 ys := accumErr t1 id toTable xs | Fail0 err => Left err
    in assemble t2 ys r
  TableName k =>
   let Right (p,t) := tableAt k top | Left e => Left e
       Succ0 t2 ys := accumErr t (ins p) toTable xs | Fail0 e => Left e
    in assemble t2 ys r
  ArrayName k =>
   let Right (p,sv) := arrayAt k top | Left e => Left e
       t            := TTbl Table empty
       Succ0 t2 ys  := accumErr t (append p sv) toTable xs | Fail0 e => Left e
    in assemble t2 ys r
assemble top []        _      = Right top

--------------------------------------------------------------------------------
--          TomlValue and Table
--------------------------------------------------------------------------------

-- facilitates pattern matching on and creating of symbol
-- tokens such as '['. We don't want to export this, as it tends
-- to interfer with regular `String` literals.
%inline
fromString : String -> TomlToken
fromString = TSym

0 AccRule : Bool -> Type -> Type
AccRule b = AccGrammar b TomlToken TomlParseError

0 Rule : Bool -> Type -> Type
Rule b = Grammar b TomlToken TomlParseError

array : Bounds -> SnocList TomlValue -> AccRule True TomlValue

table : Bounds -> TomlValue -> AccRule True TomlValue

value : AccRule True TomlValue
value (B (TVal v) _ :: xs)       _      = Succ0 v xs
value (B "[" _ :: B "]" _ :: xs) _      = Succ0 (TArr Static [<]) xs
value (B "{" _ :: B "}" _ :: xs) _      = Succ0 (TTbl Inline empty) xs
value (B "[" b :: xs)            (SA r) = succT $ array b [<] xs r
value (B "{" b :: xs)            (SA r) = succT $ table b (TTbl None empty) xs r
value xs                         _      = fail xs

array b sx xs acc@(SA r) = case value xs acc of 
  Succ0 v (B "," _ :: B "]" _ :: ys) => Succ0 (TArr Static $ sx :< v) ys
  Succ0 v (B "," _ :: ys)            => succT $ array b (sx :< v) ys r
  Succ0 v (B "]" _ :: ys)            => Succ0 (TArr Static $ sx :< v) ys
  res                                => failInParen b "[" res

key : Rule True (List1 KeyToken)
key = terminal $ \case TKey x => Just x; _ => Nothing

keyVal : AccRule True (List1 KeyToken,TomlValue)
keyVal (B (TKey x) _ :: B "=" _ :: xs) (SA r) = (x,) <$> succT (value xs r)
keyVal (B (TKey _) _ :: x :: xs)       _      = expected x.bounds "="
keyVal xs                              _      = fail xs

inline : TomlValue -> TomlValue
inline (TTbl _ y) = TTbl Inline y
inline v          = v

table b tbl xs acc@(SA r) = case keyVal xs acc of 
  Succ0 (bk,v) ys => case fromEither {b = True} ys $ tryInsert bk v tbl of
    Succ0 tbl1 (B "," _ :: ys)            => succT $ table b tbl1 ys r
    Succ0 tbl1 (B "}" _ :: ys)            => Succ0 (inline tbl1) ys
    res                                   => failInParen b "{" res
  res => failInParen b "{" res

item : Rule True TomlItem
item (B "[" b1 :: xs)  = TableName <$> succT (before key "]" xs)
item (B "[[" b1 :: xs) = ArrayName <$> succT (before key "]]" xs)
item ts                = uncurry KeyVal <$> acc keyVal ts

items :
     SnocList TomlItem
  -> (ts : List $ Bounded TomlToken)
  -> (0 acc : SuffixAcc ts)
  -> Either (Bounded TomlErr) (List TomlItem)
items sx []             _      = Right $ sx <>> []
items sx (B NL _ :: xs) (SA r) = items sx xs r
items sx xs             (SA r) = case item xs of
  Succ0 i (B NL _ :: xs) => items (sx :< i) xs r
  Succ0 i (x::xs)        => unexpected x
  Succ0 i []             => Right (sx <>> [i])
  Fail0 err              => Left err

export
parse : Origin -> String -> Either (ParseError TomlParseError) TomlValue
parse o s = mapFst (toParseError o s) $ do
  ts <- lexToml s
  ti <- items [<] ts suffixAcc
  assemble (TTbl Table empty) ti suffixAcc
