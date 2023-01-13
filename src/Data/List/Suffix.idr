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
data Suffix : (strict : Bool) -> (as : List a) -> (bs : List a) -> Type where
  ||| Every list is a non-strict suffix of itself
  Same : Suffix False as as

  ||| If `as` is a suffix of `bs`, then `as` is a strict suffix
  ||| of `b :: bs`, for all `b`s.
  |||
  ||| Note: We let the *caller* of `Cons` decide whether they
  ||| need the strictness flag to be set or not.
  Cons : Suffix b1 as bs -> Suffix b2 as (b :: bs)

public export
suffixToNat : Suffix b as bs -> Nat
suffixToNat Same     = Z
suffixToNat (Cons x) = S $ suffixToNat x

--------------------------------------------------------------------------------
--          Utilities
--------------------------------------------------------------------------------

||| Alias for `Cons` but with the strictness flag of the result
||| explicitly set to `True`. Use this in case of Idris2 complaining
||| about unbound implicits.
public export %inline
cons : Suffix b1 as bs -> Suffix True as (b :: bs)
cons = Cons

||| Alias for `Cons Same` but with the strictness flag of the result
||| explicitly set to `True`.
public export %inline
cons1 : Suffix True as (a :: as)
cons1 = Cons Same

||| The empty list is a suffix of any list.
export
nil : (as : List a) -> Suffix False [] as
nil []        = Same
nil (x :: xs) = Cons $ nil xs

||| We can always set the strictness to `False`.
export
weaken : Suffix b as bs -> Suffix False as bs
weaken Same     = Same
weaken (Cons x) = Cons x

||| We can always set the strictness to `False`.
export
weakens : Suffix True as bs -> Suffix b as bs
weakens (Cons x) = Cons x
weakens Same impossible

||| If `h :: t` is a suffix of `bs`, then `t` is a strict
||| suffix of `bs`.
export
consLeft : Suffix b (h :: t) bs -> Suffix True t bs
consLeft Same     = Cons Same
consLeft (Cons x) = Cons (consLeft x)

||| Same as `consLeft`, but we don't care about the
||| strictness guarantees.
export
consLeft_ : Suffix b (h :: t) bs -> Suffix b t bs
consLeft_ = weakens . consLeft

export
and1 : {b1,b2 : Bool} -> Suffix b1 as bs -> Suffix (b1 && b2) as bs
and1 {b1 = True}  {b2 = True}  x = x
and1 {b1 = True}  {b2 = False} x = weakens x
and1 {b1 = False} {b2 = True}  x = x
and1 {b1 = False} {b2 = False} x = x

export
or1 : {b1,b2 : Bool} -> Suffix (b1 || b2) as bs -> Suffix b1 as bs
or1 {b1 = True}  {b2 = True}  x = x
or1 {b1 = True}  {b2 = False} x = x
or1 {b1 = False} {b2 = True}  x = weaken x
or1 {b1 = False} {b2 = False} x = x

export
and2 : {b1,b2 : Bool} -> Suffix b2 as bs -> Suffix (b1 && b2) as bs
and2 {b1 = True}  {b2 = True}  x = x
and2 {b1 = True}  {b2 = False} x = x
and2 {b1 = False} {b2 = True}  x = weakens x
and2 {b1 = False} {b2 = False} x = x

export
or2 : {b1,b2 : Bool} -> Suffix (b1 || b2) as bs -> Suffix b2 as bs
or2 {b1 = True}  {b2 = True}  x = x
or2 {b1 = True}  {b2 = False} x = weaken x
or2 {b1 = False} {b2 = True}  x = x
or2 {b1 = False} {b2 = False} x = x

export
swapOr : {b1,b2 : Bool} -> Suffix (b1 || b2) as bs -> Suffix (b2 || b1) as bs
swapOr x = rewrite orCommutative b2 b1 in x

export
swapAnd : {b1,b2 : Bool} -> Suffix (b1 && b2) as bs -> Suffix (b2 && b1) as bs
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
trans : Suffix b1 as bs -> Suffix b2 bs cs -> Suffix (b1 || b2) as cs
trans Same Same         = Same
trans Same     (Cons x) = Cons (trans x Same)
trans (Cons x) Same     = Cons (trans x Same)
trans (Cons x) (Cons y) = Cons $ trans x (consLeft y)

||| `Suffix False` is a reflexive relation on lists.
export
Reflexive (List a) (Suffix False) where
  reflexive = Same

||| `Suffix False` is a transitive relation on lists.
export
Transitive (List a) (Suffix False) where
  transitive = trans

||| `Suffix True` is a transitive relation on lists.
export
Transitive (List a) (Suffix True) where
  transitive = trans

infixr 3 ~>,~?>,~~>

||| Operator alias for `trans`.
export %inline
(~>) : Suffix b1 as bs -> Suffix b2 bs cs -> Suffix (b1 || b2) as cs
(~>) = trans

0 sameBool : (b : Bool) -> b === (b || b)
sameBool False = Refl
sameBool True  = Refl

||| Operator alias for `trans` where strictnes of the second
||| suffix dominates.
export %inline
0 (~~>) : Suffix b1 as bs -> Suffix b2 bs cs -> Suffix b2 as cs
(~~>) {b1 = True}  {b2 = True} x y = trans x y
(~~>) {b1 = True}  {b2 = False} x y = weaken $ trans x y
(~~>) {b1 = False} {b2 = True} x y = trans x y
(~~>) {b1 = False} {b2 = False} x y = trans x y

||| Operator alias for `trans` where the result is always non-strict
||| suffix dominates.
export %inline
0 (~?>) : Suffix b1 as bs -> Suffix b2 bs cs -> Suffix False as cs
(~?>) x y = weaken $ trans x y

--------------------------------------------------------------------------------
--          Accessibility
--------------------------------------------------------------------------------

public export
SuffixAcc : (as : List a) -> Type
SuffixAcc as = Accessible (Suffix True) as

||| Proof of well foundedness:
|||
||| `Suffix True` is well founded, since every chain
||| a(0), a(1), ..., where a(i+1) is a strict suffix of a(i) for all i
||| must be finite.
export
ssAcc : (as : List a) ->  SuffixAcc as
ssAcc as = Access (acc as)
  where
    acc : (vs : List a) -> (bs : List a) -> Suffix True bs vs -> SuffixAcc bs
    acc (h :: t) bs (Cons x) = Access $ \y,prf => acc t y (prf ~> x)

export
WellFounded (List a) (Suffix True) where
  wellFounded = ssAcc
