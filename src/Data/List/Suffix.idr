module Data.List.Suffix

import Control.Relation
import public Data.Bool.Rewrite

%default total

||| Proof that a list is a (possibly strict) suffix of another list.
|||
||| Performance: Values of this type are optimized to integers at runtime.
public export
data Suffix : (strict : Bool) -> (xs,ys : List a) -> Type where
  ||| Every list is a (non-strict) suffix of itself.
  Same   : Suffix False xs xs

  ||| If a non-empty list `xs` is a suffix of `ys`, then the tail of
  ||| `xs` is a strict suffix of `ys`.
  Uncons : Suffix b (h :: t) cs -> Suffix b2 t cs

%builtin Natural Suffix

export
Uninhabited (Suffix b (h :: t) []) where
  uninhabited Same impossible
  uninhabited (Uncons x) = uninhabited x

export
Uninhabited (Suffix True xs []) where
  uninhabited (Uncons x) = uninhabited x

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

||| Converts a `Suffix` to a natural number, representing
||| the number of items dropped from the original list.
|||
||| Performance: This is the identity function at runtime.
public export
toNat : Suffix b xs ys -> Nat
toNat Same       = Z
toNat (Uncons x) = S $toNat x

public export %inline
Cast (Suffix b xs ys) Nat where cast = toNat

public export
swapOr : {0 x,y : _} -> Suffix (x || y) xs ys -> Suffix (y || x) xs ys
swapOr = swapOr (\k => Suffix k xs ys)

public export %inline
orSame : {0 x : _} -> Suffix (x || x) xs ys -> Suffix x xs ys
orSame = orSame (\k => Suffix k xs ys)

public export %inline
orTrue : {0 x : _} -> Suffix (x || True) xs ys -> Suffix True xs ys
orTrue = orTrue (\k => Suffix k xs ys)

public export %inline
orFalse : {0 x : _} -> Suffix (x || False) xs ys -> Suffix x xs ys
orFalse = orFalse (\k => Suffix k xs ys)

public export %inline
swapAnd : {0 x,y : _} -> Suffix (x && y) xs ys -> Suffix (y && x) xs ys
swapAnd = swapAnd (\k => Suffix k xs ys)

public export %inline
andSame : {0 x : _} -> Suffix (x && x) xs ys -> Suffix x xs ys
andSame = andSame (\k => Suffix k xs ys)

public export %inline
andTrue : {0 x : _} -> Suffix (x && True) xs ys -> Suffix x xs ys
andTrue = andTrue (\k => Suffix k xs ys)

public export %inline
andFalse : {0 x : _} -> Suffix (x && False) xs ys -> Suffix False xs ys
andFalse = andFalse (\k => Suffix k xs ys)

||| Every `Suffix` can be converted to a non-strict one.
|||
||| Performance: This is the identity function at runtime.
public export
weaken : Suffix b xs ys -> Suffix False xs ys
weaken Same       = Same
weaken (Uncons x) = Uncons x

||| A strict `Suffix` can be converted to a non-strict one.
|||
||| Performance: This is the identity function at runtime.
public export
weakens : Suffix True xs ys -> Suffix b xs ys
weakens (Uncons x) = Uncons x
weakens Same impossible

public export
unconsBoth : Suffix b (y :: ys) (x :: xs) -> Suffix False ys xs
unconsBoth Same       = Same
unconsBoth (Uncons z) = Uncons $ unconsBoth z

public export
unconsRight : Suffix True ys (x :: xs) -> Suffix False ys xs
unconsRight (Uncons x) = unconsBoth x

public export
and1 : Suffix b1 xs ys -> Suffix (b1 && b2) xs ys
and1 Same       = Same
and1 (Uncons x) = Uncons x

public export
and2 : Suffix b2 xs ys -> Suffix (b1 && b2) xs ys
and2 s = swapAnd (and1 s)

--------------------------------------------------------------------------------
--          Relations
--------------------------------------------------------------------------------

||| `Suffix` is a reflexive and transitive relation.
|||
||| Performance: This is integer addition at runtime.
public export
trans : Suffix b1 xs ys -> Suffix b2 ys cs -> Suffix (b1 || b2) xs cs
trans Same y       = y
trans (Uncons x) t = Uncons $ trans x t

%transform "suffixTransPlus" Suffix.trans x y = believe_me (toNat x + toNat y)

||| `Suffix False` is a reflexive relation on lists.
public export %inline
Reflexive (List a) (Suffix False) where
  reflexive = Same

||| `Suffix False` is a transitive relation on lists.
public export %inline
Transitive (List a) (Suffix False) where
  transitive = trans

||| `Suffix True` is a transitive relation on lists.
public export %inline
Transitive (List a) (Suffix True) where
  transitive = trans


infixr 0 ~>,~?>,~~>

infixl 0 <~,<~~

||| Operator alias for `trans`.
public export %inline
(~>) : Suffix b1 xs ys -> Suffix b2 ys zs -> Suffix (b1 || b2) xs zs
(~>) = trans

||| Flipped version of `(~>)`.
public export %inline
(<~) : Suffix b1 ys zs -> Suffix b2 xs ys -> Suffix (b1 || b2) xs zs
x <~ y = swapOr $ trans y x

||| Operator alias for `trans` where the result is always non-strict
public export %inline
(~?>) : Suffix b1 xs ys -> Suffix b2 ys zs -> Suffix False xs zs
(~?>) x y = weaken $ x ~> y

||| Operator alias for `trans` where the strictness of the first
||| `Suffix` dominates.
public export %inline
(~~>) : Suffix b1 xs ys -> Suffix True ys zs -> Suffix b1 xs zs
(~~>) x y = weakens $ y <~ x

||| Operator alias for `trans` where the strictness of the second
||| `Suffix` dominates.
public export %inline
(<~~) : Suffix b1 ys zs -> Suffix True xs ys -> Suffix b1 xs zs
(<~~) x y = weakens $ y ~> x

--------------------------------------------------------------------------------
--          SuffixAcc
--------------------------------------------------------------------------------

public export
data SuffixAcc : (ts : List t) -> Type where
  SA :
       {0 t  : Type}
    -> {0 ts : List t}
    -> ({0 ys : List t} -> {auto p : Suffix True ys ts} -> SuffixAcc ys)
    -> SuffixAcc ts

sa :
     {0 t  : Type}
  -> {0 ts : List t}
  -> ({0 ys : List t} -> (p : Suffix True ys ts) -> SuffixAcc ys)
  -> SuffixAcc ts
sa f = SA $ f %search

acc' : (ts : List t) -> Suffix False qs ts -> SuffixAcc qs
acc' []        Same       = sa $ \v => absurd v
acc' []        (Uncons x) = absurd x
acc' (x :: xs) tt         = sa $ \v => acc' xs (unconsRight $ v ~> tt)

export
suffixAcc : {ts : List t} -> SuffixAcc ts
suffixAcc = acc' ts Same
