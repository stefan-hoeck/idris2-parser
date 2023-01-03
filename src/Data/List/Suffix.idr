||| The predicates in this module are very useful for writing
||| provably total combinators that consume a list of values
||| from beginning to end (for instance: parsers!).
module Data.List.Suffix

import Data.Bool
import Data.Maybe
import public Control.Relation
import public Control.WellFounded
import public Data.Nat

%default total

--------------------------------------------------------------------------------
--          Suffix Predicate
--------------------------------------------------------------------------------

||| Proof that `as` is a suffix of `bs`.
|||
||| The `strict` flag reflects whether `as` is provably a strict
||| suffix or not.
public export
data Suffix_ : (strict : Bool) -> (as : List a) -> (bs : List a) -> Type where
  ||| Every list is a non-strict suffix of itself
  Same : Suffix_ False as as

  ||| If `as` is a suffix of `bs`, then `as` is a strict suffix
  ||| of `b :: bs`, for all `b`s.
  |||
  ||| Note: We let the *caller* of `Cons` decide whether they
  ||| need the strictness flag to be set or not.
  Cons : Suffix_ b1 as bs -> Suffix_ b2 as (b :: bs)

||| Alias for `Suffix_ False`.
public export
Suffix : (as,bs : List a) -> Type
Suffix = Suffix_ False

||| Alias for `Suffix_ True`.
public export
StrictSuffix : (as,bs : List a) -> Type
StrictSuffix = Suffix_ True

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Alias for `Cons` but with the strictness flag of the result
||| explicitly set to `True`. Use this in case of Idris2 complaining
||| about unbound implicits.
public export %inline
cons : Suffix_ b1 as bs -> StrictSuffix as (b :: bs)
cons = Cons

||| Alias for `Cons Same` but with the strictness flag of the result
||| explicitly set to `True`.
public export %inline
cons1 : StrictSuffix as (a :: as)
cons1 = Cons Same

||| The empty list is a suffix of any list.
export
nil : (as : List a) -> Suffix [] as
nil []        = Same
nil (x :: xs) = Cons $ nil xs

||| We can always set the strictness to `False`.
export
weaken : Suffix_ b as bs -> Suffix as bs
weaken Same     = Same
weaken (Cons x) = Cons (weaken x)

||| We can always set the strictness to `False`.
export
weakenS : StrictSuffix as bs -> Suffix_ b as bs
weakenS (Cons x) = Cons x
weakenS Same impossible

||| If `h :: t` is a suffix of `bs`, then `t` is a strict
||| suffix of `bs`.
export
consLeft : Suffix_ b (h :: t) bs -> StrictSuffix t bs
consLeft Same     = Cons Same
consLeft (Cons x) = Cons (consLeft x)

||| Same as `consLeft`, but we don't care about the
||| strictness guarantees.
export
consLeft_ : Suffix_ b (h :: t) bs -> Suffix_ b t bs
consLeft_ = weakenS . consLeft

export
and1 : {b1,b2 : Bool} -> Suffix_ b1 as bs -> Suffix_ (b1 && b2) as bs
and1 {b1 = True}  {b2 = True}  x = x
and1 {b1 = True}  {b2 = False} x = weakenS x
and1 {b1 = False} {b2 = True}  x = x
and1 {b1 = False} {b2 = False} x = x

export
or1 : {b1,b2 : Bool} -> Suffix_ (b1 || b2) as bs -> Suffix_ b1 as bs
or1 {b1 = True}  {b2 = True}  x = x
or1 {b1 = True}  {b2 = False} x = x
or1 {b1 = False} {b2 = True}  x = weaken x
or1 {b1 = False} {b2 = False} x = x

export
and2 : {b1,b2 : Bool} -> Suffix_ b2 as bs -> Suffix_ (b1 && b2) as bs
and2 {b1 = True}  {b2 = True}  x = x
and2 {b1 = True}  {b2 = False} x = x
and2 {b1 = False} {b2 = True}  x = weakenS x
and2 {b1 = False} {b2 = False} x = x

export
or2 : {b1,b2 : Bool} -> Suffix_ (b1 || b2) as bs -> Suffix_ b2 as bs
or2 {b1 = True}  {b2 = True}  x = x
or2 {b1 = True}  {b2 = False} x = weaken x
or2 {b1 = False} {b2 = True}  x = x
or2 {b1 = False} {b2 = False} x = x

export
swapOr : {b1,b2 : Bool} -> Suffix_ (b1 || b2) as bs -> Suffix_ (b2 || b1) as bs
swapOr x = rewrite orCommutative b2 b1 in x

export
swapAnd : {b1,b2 : Bool} -> Suffix_ (b1 && b2) as bs -> Suffix_ (b2 && b1) as bs
swapAnd x = rewrite andCommutative b2 b1 in x

--------------------------------------------------------------------------------
--          Relations
--------------------------------------------------------------------------------

||| Proof of transitivity.
|||
||| If `as` is a suffix of `bs` and `bs` is a suffix of `cs`,
||| then `as` is a suffix of `cs`. If one of the two relations is
||| strict, then `as` is a strict suffix of `cs`.
export
trans : Suffix_ b1 as bs -> Suffix_ b2 bs cs -> Suffix_ (b1 || b2) as cs
trans Same Same         = Same
trans Same     (Cons x) = Cons (trans x Same)
trans (Cons x) Same     = Cons (trans x Same)
trans (Cons x) (Cons y) = Cons $ trans x (consLeft y)

||| `Suffix` is a reflexive relation on lists.
export
Reflexive (List a) Suffix where
  reflexive = Same

||| `Suffix` is a transitive relation on lists.
export
Transitive (List a) Suffix where
  transitive = trans

||| `StrictSuffix` is a transitive relation on lists.
export
Transitive (List a) StrictSuffix where
  transitive = trans

infixr 3 ~>,~?>,~~>

||| Operator alias for `trans`.
export %inline
(~>) : Suffix_ b1 as bs -> Suffix_ b2 bs cs -> Suffix_ (b1 || b2) as cs
(~>) = trans

0 sameBool : (b : Bool) -> b === (b || b)
sameBool False = Refl
sameBool True  = Refl

||| Operator alias for `trans` where strictnes of the second
||| suffix dominates.
export %inline
0 (~~>) : Suffix_ b1 as bs -> Suffix_ b2 bs cs -> Suffix_ b2 as cs
(~~>) {b1 = True}  {b2 = True} x y = trans x y
(~~>) {b1 = True}  {b2 = False} x y = weaken $ trans x y
(~~>) {b1 = False} {b2 = True} x y = trans x y
(~~>) {b1 = False} {b2 = False} x y = trans x y

||| Operator alias for `trans` where the result is always non-strict
||| suffix dominates.
export %inline
0 (~?>) : Suffix_ b1 as bs -> Suffix_ b2 bs cs -> Suffix_ False as cs
(~?>) x y = weaken $ trans x y

--------------------------------------------------------------------------------
--          Accessibility
--------------------------------------------------------------------------------

public export
SuffixAcc : (as : List a) -> Type
SuffixAcc as = Accessible StrictSuffix as

||| Proof of well foundedness:
|||
||| `StrictSuffix` is well founded, since every chain
||| a(0), a(1), ..., where a(i+1) is a strict suffix of a(i) for all i
||| must be finite.
export
ssAcc : (as : List a) ->  SuffixAcc as
ssAcc as = Access (acc as)
  where
    acc : (vs : List a) -> (bs : List a) -> StrictSuffix bs vs -> SuffixAcc bs
    acc (h :: t) bs (Cons x) = Access $ \y,prf => acc t y (prf ~> x)

export
WellFounded (List a) StrictSuffix where
  wellFounded = ssAcc
