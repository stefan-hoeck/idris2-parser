module Data.Nat.LEQ

import Control.Relation
import Data.Nat
import public Data.Bool.Rewrite

%default total

||| Proof that one natural number is less than or equal than
||| another one. This defined differently that `Data.Nat.LTE`,
||| but similar to `Data.List.Suffix`, as it works well during
||| iteration.
public export
data LEQ : Bool -> Nat -> Nat -> Type where
  Same : LEQ False n n
  LT   : {0 b1,b2 : Bool} -> LEQ b1 (S k) n -> LEQ b2 k n

%builtin Natural LEQ

export
Uninhabited (LEQ b (S k) 0) where
  uninhabited Same impossible
  uninhabited (LT x) = uninhabited x

export
Uninhabited (LEQ True k 0) where
  uninhabited (LT x) = uninhabited x

||| Strict version of `LT`
public export %inline
lt : LEQ b (S k) n -> LEQ True k n
lt = LT

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

||| Converts a `LEQ` to a natural number, representing
||| the number of items dropped from the original number.
|||
||| Performance: This is the identity function at runtime.
public export
toNat : LEQ b m n -> Nat
toNat Same   = Z
toNat (LT x) = S $ toNat x

public export %inline
Cast (LEQ b m n) Nat where cast = toNat

export
0 toLTE : LEQ b m n -> LTE m n
toLTE Same   = reflexive
toLTE (LT x) = lteSuccLeft $ toLTE x

export
0 toLT : LEQ True m n -> LT m n
toLT (LT x) = toLTE x

public export
swapOr : {0 x,y : _} -> LEQ (x || y) m n -> LEQ (y || x) m n
swapOr = swapOr (\k => LEQ k m n)

public export %inline
orSame : {0 x : _} -> LEQ (x || x) m n -> LEQ x m n
orSame = orSame (\k => LEQ k m n)

public export %inline
orTrue : {0 x : _} -> LEQ (x || True) m n -> LEQ True m n
orTrue = orTrue (\k => LEQ k m n)

public export %inline
orFalse : {0 x : _} -> LEQ (x || False) m n -> LEQ x m n
orFalse = orFalse (\k => LEQ k m n)

public export %inline
swapAnd : {0 x,y : _} -> LEQ (x && y) m n -> LEQ (y && x) m n
swapAnd = swapAnd (\k => LEQ k m n)

public export %inline
andSame : {0 x : _} -> LEQ (x && x) m n -> LEQ x m n
andSame = andSame (\k => LEQ k m n)

public export %inline
andTrue : {0 x : _} -> LEQ (x && True) m n -> LEQ x m n
andTrue = andTrue (\k => LEQ k m n)

public export %inline
andFalse : {0 x : _} -> LEQ (x && False) m n -> LEQ False m n
andFalse = andFalse (\k => LEQ k m n)

||| Every `LEQ` can be converted to a non-strict one.
|||
||| Performance: This is the identity function at runtime.
public export
weaken : LEQ b m n -> LEQ False m n
weaken Same   = Same
weaken (LT x) = LT x

||| A strict `LEQ` can be converted to a non-strict one.
|||
||| Performance: This is the identity function at runtime.
public export
weakens : LEQ True m n -> LEQ b m n
weakens (LT x) = LT x
weakens Same impossible

public export
ltBoth : LEQ b (S m) (S n) -> LEQ False m n
ltBoth Same   = Same
ltBoth (LT z) = LT $ ltBoth z

public export
ltRight : LEQ True m (S n) -> LEQ False m n
ltRight (LT x) = ltBoth x

public export
and1 : LEQ b1 m n -> LEQ (b1 && b2) m n
and1 Same       = Same
and1 (LT x) = LT x

public export
and2 : LEQ b2 m n -> LEQ (b1 && b2) m n
and2 s = swapAnd (and1 s)

--------------------------------------------------------------------------------
--          Relations
--------------------------------------------------------------------------------

||| `LEQ` is a reflexive and transitive relation.
|||
||| Performance: This is integer addition at runtime.
public export
trans : LEQ b1 k m -> LEQ b2 m n -> LEQ (b1 || b2) k n
trans Same y   = y
trans (LT x) t = LT $ trans x t

%inline
transp : LEQ b1 k m -> LEQ b2 m n -> LEQ (b1 || b2) k n
transp x y =  believe_me (toNat x + toNat y)

%transform "suffixTransPlus" LEQ.trans = LEQ.transp

||| `LEQ False` is a reflexive relation on natural numbers.
public export %inline
Reflexive Nat (LEQ False) where
  reflexive = Same

||| `LEQ False` is a transitive relation on natural numbers.
public export %inline
Transitive Nat (LEQ False) where
  transitive = trans

||| `LEQ True` is a transitive relation on natural numbers.
public export %inline
Transitive Nat (LEQ True) where
  transitive = trans

--------------------------------------------------------------------------------
--          LEQAcc
--------------------------------------------------------------------------------

public export
data LEQAcc : (n : Nat) -> Type where
  LA : {0 n : Nat}
    -> ({0 m : Nat} -> {auto p : LEQ True m n} -> LEQAcc m)
    -> LEQAcc n

la :
     {0 n : Nat}
  -> ({0 m : Nat} -> (p : LEQ True m n) -> LEQAcc m)
  -> LEQAcc n
la f = LA $ f %search

acc' : (n : Nat) -> LEQ False m n -> LEQAcc m
acc' 0     Same   = la $ \v => absurd v
acc' 0     (LT x) = absurd x
acc' (S k) tt     = la $ \v => acc' k (ltRight $ trans v tt)

export
leqAcc : {n : Nat} -> LEQAcc n
leqAcc = acc' n Same
