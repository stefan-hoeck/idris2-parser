module Data.Nat.LEQ.Result

import Data.Bool.Rewrite
import Data.ByteVect
import public Data.Nat.LEQ

%default total

||| Result of consuming and converting a (possibly strict) prefix
||| of an immutable byte vector.
|||
||| Use this for writing simple, high-performance tokenizers, which
||| (in the case of strict results) are guaranteed to terminate.
|||
||| @ strict : True if the length of the new byte vector is strictly smaller
|||            than the original's length
||| @ n      : the length of the original byte vector
||| @ e      : the error type in case of a failure
||| @ a      : the result type
public export
data Result : (strict : Bool) -> (n : Nat) -> (e,a : Type) -> Type where
  Succ :
       {0 b : Bool}
    -> {0 e,a : Type}
    -> {0 n : Nat}
    -> (val : a)
    -> {m   : Nat}
    -> ByteVect m
    -> {auto 0 p : LEQ b m n}
    -> Result b n e a

  Fail :
       {0 b : Bool}
    -> {0 e,a : Type}
    -> {n,stopStart : Nat}
    -> (0 start : LEQ False stopStart n)
    -> (errEnd : Nat)
    -> {auto 0 end : LEQ False errEnd stopStart}
    -> (reason : e)
    -> Result b n e a

public export
Functor (Result b n e) where
  map f (Succ v xs)    = Succ (f v) xs
  map _ (Fail st ee r) = Fail st ee r

----------------------------------------------------------------------------------
----          Conversions
----------------------------------------------------------------------------------

public export %inline
swapOr : {0 x,y : _} -> Result (x || y) n e a -> Result (y || x) n e a
swapOr = swapOr (\k => Result k n e a)

public export %inline
orSame : {0 x : _} -> Result (x || x) n e a -> Result x n e a
orSame = orSame (\k => Result k n e a)

public export %inline
orTrue : {0 x : _} -> Result (x || True) n e a -> Result True n e a
orTrue = orTrue (\k => Result k n e a)

public export %inline
orFalse : {0 x : _} -> Result (x || False) n e a -> Result x n e a
orFalse = orFalse (\k => Result k n e a)

public export %inline
swapAnd : {0 x,y : _} -> Result (x && y) n e a -> Result (y && x) n e a
swapAnd = swapAnd (\k => Result k n e a)

public export %inline
andSame : {0 x : _} -> Result (x && x) n e a -> Result x n e a
andSame = andSame (\k => Result k n e a)

public export %inline
andTrue : {0 x : _} -> Result (x && True) n e a -> Result x n e a
andTrue = andTrue (\k => Result k n e a)

public export %inline
andFalse : {0 x : _} -> Result (x && False) n e a -> Result False n e a
andFalse = andFalse (\k => Result k n e a)

public export %inline
weaken : {0 x : _} -> Result x n e a -> Result False n e a
weaken (Succ val xs @{p}) = Succ val xs @{weaken p}
weaken (Fail x y err) = Fail x y err

public export %inline
weakens : {0 x : _} -> Result True n e a -> Result x n e a
weakens (Succ val xs @{p}) = Succ val xs @{weakens p}
weakens (Fail x y err) = Fail x y err

public export %inline
and1 : {0 x : _} -> Result x n e a -> Result (x && y) n e a
and1 (Succ val xs @{p}) = Succ val xs @{and1 p}
and1 (Fail x y err) = Fail x y err

public export %inline
and2 : {0 x : _} -> Result x n e a -> Result (y && x) n e a
and2 r = swapAnd $ and1 r

public export %inline
trans :
     {n : _}
  -> Result b1 m e a
  -> (0 q : LEQ b2 m n)
  -> Result (b1 || b2) n e a
trans (Succ val bv @{p}) q = Succ val bv @{trans p q}
trans (Fail {stopStart} x y err) q =
  Fail {stopStart} (weaken $ trans x q) y err

public export %inline
succT :
      {m : _}
  ->  Result b1 n e a
  -> {auto 0 p : LEQ True n m}
  -> Result True m e a
succT r = swapOr $ trans r p

public export %inline
succF :
      {m : _}
  ->  Result b1 n e a
  -> {auto 0 p : LEQ True n m}
  -> Result False m e a
succF r = weaken $ trans r p
