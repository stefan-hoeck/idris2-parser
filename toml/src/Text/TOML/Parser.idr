module Text.TOML.Parser

import Data.List1
import Data.SortedMap
import Text.Parse.Manual
import Text.TOML.Lexer
import Text.TOML.Types

%default total

public export
data TomlItem : Type where
  TableName      : Key -> TomlItem
  TableArrayName : Key -> TomlItem
  KeyValPair     : Key -> TomlValue -> TomlItem

insertEmpty : List String -> TomlValue -> TomlValue
insertEmpty []      v = v
insertEmpty (x::xs) v = TTbl $ singleton x (insertEmpty xs v)

insertTbl : Key -> TomlValue -> TomlTable -> Either TomlErr TomlTable
insertTbl k@(h:::t) v = go h t
  where
    go : String -> List String -> TomlTable -> Either TomlErr TomlTable
    go h [] tbl = case lookup h tbl of
      Just _  => Left (Custom $ KeyExists k)
      Nothing => Right $ insert h v tbl
    go h (x::xs) tbl = case lookup h tbl of
      Just (TTbl tbl') => map (\tt => insert h (TTbl tt) tbl) (go x xs tbl')
      Just _           => Left (Custom $ KeyExists k)
      Nothing          => Right $ insert h (insertEmpty (x::xs) v) tbl

assembleTable :
     (tbl   : TomlTable)
  -> (items : List $ Bounded TomlItem)
  -> (0 acc : SuffixAcc items)
  -> Text.Parse.Res.Res False TomlItem items TomlParseError TomlTable
-- assembleTable tbl []            _      = Succ tbl []
-- assembleTable tbl (B v b :: xs) (SA r) = case v of
--   TableName ys => ?foo_0
--   TableArrayName ys => ?foo_1
--   KeyValPair ys x => case insertTbl ys x tbl of
--     Left err   => Fail (B err b)
--     Right tbl' => wsucc $ assembleTable tbl' xs r

--------------------------------------------------------------------------------
--          TomlValue and Table
--------------------------------------------------------------------------------

-- facilitates pattern matching on and creating of symbol
-- tokens such as '['. We don't want to export this, as it tends
-- to interfer with regular `Char` literals.
%inline
fromChar : Char -> TomlToken
fromChar = TSym

0 Rule : Bool -> Type -> Type
Rule b a =
     (ts : List (Bounded TomlToken))
  -> (0 acc : SuffixAcc ts)
  -> Text.Parse.Res.Res b TomlToken ts TomlParseError a

array : Bounds -> SnocList TomlValue -> Rule True TomlValue

table : Bounds -> TomlTable -> Rule True TomlValue

value : Rule True TomlValue
value (B (TVal v) _ :: xs)       _      = Succ v xs
value (B '[' _ :: B ']' _ :: xs) _      = Succ (TArr []) xs
value (B '{' _ :: B '}' _ :: xs) _      = Succ (TTbl empty) xs
value (B '[' b :: xs)            (SA r) = succ $ array b [<] xs r
value (B '{' b :: xs)            (SA r) = succ $ table b empty xs r
value xs                         _      = fail xs

array b sx xs acc@(SA r) = case value xs acc of 
  Succ v (B ',' _ :: B ']' _ :: ys) => Succ (TArr $ sx <>> [v]) ys
  Succ v (B ',' _ :: ys)            => succ $ array b (sx :< v) ys r
  Succ v (B ']' _ :: ys)            => Succ (TArr $ sx <>> [v]) ys
  res                               => failInParen b '[' res

keyVal : Rule True (Bounded Key,TomlValue)
keyVal (B (TKey x) b :: B '=' _ :: xs) (SA r) = (B x b,) <$> succ (value xs r)
keyVal (B (TKey _) _ :: x :: xs)       _      = expected x.bounds '='
keyVal xs                              _      = fail xs

table b tbl xs acc@(SA r) = case keyVal xs acc of 
  Succ (bk,v) ys =>
    let Right tbl' := insertTbl bk.val v tbl | Left err => Fail (bk $> err)
     in case ys of
       B ',' _ :: ys => succ $ table b tbl' ys r
       B '}' _ :: ys => Succ (TTbl tbl') ys
       y :: ys       => unexpected y
       []            => unclosed b '{'
  res => failInParen b '{' res

item : Rule True (Bounded TomlItem)
item (B '[' x :: B (TKey k) y :: B ']' z :: xs) _ =
  Succ (B (TableName k) (x <+> y <+> z)) xs
item (B '[' v :: B '[' w :: B (TKey k) x :: B ']' y :: B ']' z :: xs) _ =
  Succ (B (TableArrayName k) (v <+> w <+> x <+> y <+> z)) xs
item ts acc = (\(B k b,v) => B (KeyValPair k v) b) <$> keyVal ts acc

items :
     SnocList (Bounded TomlItem)
  -> (ts : List (Bounded TomlToken))
  -> (0 acc : SuffixAcc ts)
  -> Either (Bounded TomlErr) (List $ Bounded TomlItem)
items sx []       acc = Right $ sx <>> []
items sx [B NL _] acc = Right $ sx <>> []
items sx xs       acc@(SA r) = case item xs acc of
  Succ i (B NL _ :: xs) => items (sx :< i) xs r
  Res.Succ i (x::xs)    => Left (Unexpected <$> x)
  Succ i []             => Right (sx <>> [i])
  Fail err              => Left err
