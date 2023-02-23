module Data.List.Shift

import Data.Bool.Rewrite
import Data.List.Suffix
import Data.Nat

%default total

||| Witness that a pair of a snoclist and a list
||| is the result of shifting values from the head of
||| an initial list to the tail of an initial snoclist.
|||
||| This data type is a witness for what a lexer does:
||| taking a finite number of elements from the head of a
||| list and appending them to the tail of a snoclist.
|||
||| By carrying around such a proof, we guarantee that no
||| character is lost during lexing, and that the order of
||| characters does not change during lexing.
|||
||| @ strict : `True` if at least one element was shifted
||| @ sx     : the current snoclist
||| @ xs     : the current list
||| @ giro   : the initial snoclist
||| @ orig   : the initial list
public export
data Shift :
     (strict : Bool)
  -> (t      : Type)
  -> (sx     : SnocList t)
  -> (xs     : List t)
  -> (giro   : SnocList t)
  -> (orig   : List t)
  -> Type where
  [search strict xs giro orig]

  ||| Doing nothing results in a non-strict `Shift`
  Same : 
       {0 t : Type}
    -> {0 sx : SnocList t}
    -> {0 xs : List t}
    -> Shift False t sx xs sx xs

  ||| We arrive at a new result by shifting one more value.
  SH   :
       {0 t : Type}
    -> {0 b1,b2 : Bool}
    -> {0 x : t}
    -> {0 sx,sy : SnocList t}
    -> {0 xs,ys : List t}
    -> Shift b1 t sx (x :: xs) sy ys
    -> Shift b2 t (sx :< x) xs sy ys

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

||| Converts a `Shift` to a natural number, representing
||| the number of items dropped from the original list.
|||
||| Performance: This is the identity function at runtime.
public export
toNat : {0 b : Bool} -> Shift b t sx xs sy ys -> Nat
toNat Same   = Z
toNat (SH x) = S $ toNat x

public export %inline
Cast (Shift b t sx xs sy ys) Nat where cast = toNat

public export
swapOr : {0 x,y : _} -> Shift (x || y) t sx xs sy ys -> Shift (y || x) t sx xs sy ys
swapOr = swapOr (\k => Shift k t sx xs sy ys)

public export %inline
orSame : {0 x : _} -> Shift (x || x) t sx xs sy ys -> Shift x t sx xs sy ys
orSame = orSame (\k => Shift k t sx xs sy ys)

public export %inline
orTrue : {0 x : _} -> Shift (x || True) t sx xs sy ys -> Shift True t sx xs sy ys
orTrue = orTrue (\k => Shift k t sx xs sy ys)

public export %inline
orFalse : {0 x : _} -> Shift (x || False) t sx xs sy ys -> Shift x t sx xs sy ys
orFalse = orFalse (\k => Shift k t sx xs sy ys)

public export %inline
swapAnd : {0 x,y : _} -> Shift (x && y) t sx xs sy ys -> Shift (y && x) t sx xs sy ys
swapAnd = swapAnd (\k => Shift k t sx xs sy ys)

public export %inline
andSame : {0 x : _} -> Shift (x && x) t sx xs sy ys -> Shift x t sx xs sy ys
andSame = andSame (\k => Shift k t sx xs sy ys)

public export %inline
andTrue : {0 x : _} -> Shift (x && True) t sx xs sy ys -> Shift x t sx xs sy ys
andTrue = andTrue (\k => Shift k t sx xs sy ys)

public export %inline
andFalse : {0 x : _} -> Shift (x && False) t sx xs sy ys -> Shift False t sx xs sy ys
andFalse = andFalse (\k => Shift k t sx xs sy ys)

||| Every `Shift` can be converted to a non-strict one.
|||
||| Performance: This is the identity function at runtime.
public export
weaken : {0 b : Bool} -> Shift b t sx xs sy ys -> Shift False t sx xs sy ys
weaken Same   = Same
weaken (SH x) = SH x

||| A strict `Shift` can be converted to a non-strict one.
|||
||| Performance: This is the identity function at runtime.
public export
weakens : {0 b : Bool} -> Shift True t sx xs sy ys -> Shift b t sx xs sy ys
weakens (SH x) = SH x
weakens Same impossible

||| A `Shift` can be converted to a `Suffix`.
|||
||| Performance: This is the identity function at runtime.
public export
suffix : {0 b : Bool} -> Shift b t sx xs sy ys -> Suffix b xs ys
suffix Same   = Same
suffix (SH x) = Uncons $ suffix x

public export
and1 : Shift b1 t sx xs sy ys -> Shift (b1 && b2) t sx xs sy ys
and1 Same   = Same
and1 (SH x) = SH x

public export
and2 : Shift b2 t sx xs sy ys -> Shift (b1 && b2) t sx xs sy ys
and2 s = swapAnd (and1 s)

||| `Shift` is a reflexive and transitive relation.
|||
||| Performance: This is integer addition at runtime.
public export
trans :
     Shift b1 t sx xs sy ys
  -> Shift b2 t sy ys sz zs
  -> Shift (b1 || b2) t sx xs sz zs
trans Same y   = y
trans (SH x) y = SH $ trans x y

%inline
transp :
     Shift b1 t sx xs sy ys
  -> Shift b2 t sy ys sz zs
  -> Shift (b1 || b2) t sx xs sz zs
transp x y = believe_me (toNat x + toNat y)

%transform "shiftTransPlus" Shift.trans = Shift.transp
