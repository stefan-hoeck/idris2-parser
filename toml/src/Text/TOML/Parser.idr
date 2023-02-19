module Text.TOML.Parser

import Text.PrettyPrint.Bernardy
import Data.List1
import Data.SortedMap
import Text.Parse.Manual
import Text.TOML.Lexer
import Text.TOML.Types

%default total

public export
data TomlItem : Type where
  TableName      : List1 KeyToken -> TomlItem
  TableArrayName : List1 KeyToken -> TomlItem
  KeyValPair     : List1 KeyToken -> TomlValue -> TomlItem

insertEmpty : KeyToken -> List KeyToken -> TomlValue -> TomlTable
insertEmpty s []      v = singleton s.key v
insertEmpty s (x::xs) v = singleton s.key (TTbl False $ insertEmpty x xs v)

keyErr : SnocList KeyToken -> KeyToken -> Either (Bounded TomlErr) a
keyErr sx x =
  let ks := sx <>> [x]
   in Left (B (Custom $ ValueExists ks) $ concatMap bounds ks)

insertTbl :
     List1 KeyToken
  -> TomlValue
  -> TomlTable
  -> Either (Bounded TomlErr) TomlTable
insertTbl (h:::t) v = go [<] h t
  where
    go :
         SnocList KeyToken
      -> KeyToken
      -> List KeyToken
      -> TomlTable
      -> Either (Bounded TomlErr) TomlTable
    go sk h [] tbl = case lookup h.key tbl of
      Just _  => keyErr sk h
      Nothing => Right $ insert h.key v tbl
    go sk h (x::xs) tbl = case lookup h.key tbl of
      Just (TTbl False tbl') =>
        map (\tt => insert h.key (TTbl False tt) tbl) (go (sk :< h) x xs tbl')
      Just _                 => keyErr sk h
      Nothing                =>
        Right $ insert h.key (TTbl False $ insertEmpty x xs v) tbl

toTable : TomlTable -> TomlItem -> AccumRes TomlTable (Bounded TomlErr)
toTable tbl (KeyValPair xs x) = either Error Cont $ insertTbl xs x tbl
toTable _   _                 = Done

toArray :
     Key
  -> (SnocList TomlValue, TomlTable)
  -> TomlItem
  -> AccumRes (SnocList TomlValue, TomlTable) (Bounded TomlErr)
toArray k (sv,tt) ti = case ti of
  KeyValPair k2 x   => either Error (\y => Cont (sv,y)) $ insertTbl k2 x tt
  TableArrayName k2 =>
    if k == map key k2 then Cont (sv :< TTbl True tt, empty) else Done
  TableName _       => Done

toVal : (SnocList TomlValue, TomlTable) -> TomlValue
toVal (sv,tbl) = TArr $ sv <>> [TTbl True tbl]

assembleTable :
     (top  : TomlTable)
  -> (items : List TomlItem)
  -> (0 acc : SuffixAcc items)
  -> Either (Bounded TomlErr) TomlTable
assembleTable top (x :: xs) (SA r) = case x of
  KeyValPair k v =>
    let Right t1 := insertTbl k v top | Left err => Left err
        Succ0 t2 ys := accumErr t1 id toTable xs | Fail0 err => Left err
     in assembleTable t2 ys r
  TableName k      => 
    let Succ0 v ys := accumErr empty (TTbl True) toTable xs | Fail0 e => Left e
        Right top2 := insertTbl k v top | Left e => Left e
     in assembleTable top2 ys r
  TableArrayName k =>
    let Succ0 v ys := accumErr ([<],empty) toVal (toArray $ map key k) xs
          | Fail0 e => Left e
        Right top2 := insertTbl k v top | Left e => Left e
     in assembleTable top2 ys r
assembleTable top []        _      = Right top

--------------------------------------------------------------------------------
--          TomlValue and Table
--------------------------------------------------------------------------------

-- facilitates pattern matching on and creating of symbol
-- tokens such as '['. We don't want to export this, as it tends
-- to interfer with regular `String` literals.
%inline
fromString : String -> TomlToken
fromString = TSym

0 Rule : Bool -> Type -> Type
Rule b a =
     (ts : List (Bounded TomlToken))
  -> (0 acc : SuffixAcc ts)
  -> Res b TomlToken ts TomlParseError a

array : Bounds -> SnocList TomlValue -> Rule True TomlValue

table : Bounds -> TomlTable -> Rule True TomlValue

value : Rule True TomlValue
value (B (TVal v) _ :: xs)       _      = Succ0 v xs
value (B "[" _ :: B "]" _ :: xs) _      = Succ0 (TArr []) xs
value (B "{" _ :: B "}" _ :: xs) _      = Succ0 (TTbl True empty) xs
value (B "[" b :: xs)            (SA r) = succT $ array b [<] xs r
value (B "{" b :: xs)            (SA r) = succT $ table b empty xs r
value xs                         _      = fail xs

array b sx xs acc@(SA r) = case value xs acc of 
  Succ0 v (B "," _ :: B "]" _ :: ys) => Succ0 (TArr $ sx <>> [v]) ys
  Succ0 v (B "," _ :: ys)            => succT $ array b (sx :< v) ys r
  Succ0 v (B "]" _ :: ys)            => Succ0 (TArr $ sx <>> [v]) ys
  res                                => failInParen b "[" res

keyVal : Rule True (List1 KeyToken,TomlValue)
keyVal (B (TKey x) _ :: B "=" _ :: xs) (SA r) = (x,) <$> succT (value xs r)
keyVal (B (TKey _) _ :: x :: xs)       _      = expected x.bounds "="
keyVal xs                              _      = fail xs

table b tbl xs acc@(SA r) = case keyVal xs acc of 
  Succ0 (bk,v) ys => case fromEither {b = True} ys $ insertTbl bk v tbl of
    Succ0 tbl1 (B "," _ :: ys) => succT $ table b tbl1 ys r
    Succ0 tbl1 (B "}" _ :: ys) => Succ0 (TTbl True tbl1) ys
    res                        => failInParen b "{" res
  res => failInParen b "{" res

item : Rule True TomlItem
item (B "[" b1 :: xs) _ = case xs of
  B (TKey k) _ :: B "]" _ :: r => Succ0 (TableName k) r
  B (TKey k) _ :: B NL  _ :: r => unclosed b1 "["
  B (TKey k) _ :: B _   b :: r => expected b "]"
  B NL b :: r                  => unclosed b1 "["
  B _ b :: r                   => custom b ExpectedKey
  []                           => unclosed b1 "["
item (B "[[" b1 :: xs) _ = case xs of
  B (TKey k) _ :: B "]]" _ :: r => Succ0 (TableArrayName k) r
  B (TKey k) _ :: B NL   _ :: r => unclosed b1 "[["
  B (TKey k) _ :: B _    b :: r => expected b "]]"
  B NL _ :: r                   => unclosed b1 "[["
  B _ b :: r                    => custom b ExpectedKey
  []                            => unclosed b1 "[["
item ts acc = uncurry KeyValPair <$> keyVal ts acc

items :
     SnocList TomlItem
  -> (ts : List $ Bounded TomlToken)
  -> (0 acc : SuffixAcc ts)
  -> Either (Bounded TomlErr) (List TomlItem)
items sx []             _      = Right $ sx <>> []
items sx (B NL _ :: xs) (SA r) = items sx xs r
items sx xs       acc@(SA r)   = case item xs acc of
  Succ0 i (B NL _ :: xs) => items (sx :< i) xs r
  Succ0 i (x::xs)        => Left (Unexpected <$> x)
  Succ0 i []             => Right (sx <>> [i])
  Fail0 err              => Left err

export
parse : Origin -> String -> Either (FileContext,TomlErr) TomlTable
parse o s = mapFst (fromBounded o) $ do
  ts <- lexToml s
  ti <- items [<] ts suffixAcc
  assembleTable empty ti suffixAcc
