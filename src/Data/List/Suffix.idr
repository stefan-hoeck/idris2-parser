module Data.List.Suffix

import Control.Relation
import Data.Bool

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
and2 s = rewrite andCommutative b1 b2 in (and1 s)

export
0 orCommFD : (b1 || b2) === (Force b2 || Delay b1)
orCommFD {b1 = False} {b2 = False} = Refl
orCommFD {b1 = False} {b2 = True} = Refl
orCommFD {b1 = True} {b2 = False} = Refl
orCommFD {b1 = True} {b2 = True} = Refl

export
0 andCommFD : (b1 && b2) === (Force b2 && Delay b1)
andCommFD {b1 = False} {b2 = False} = Refl
andCommFD {b1 = False} {b2 = True} = Refl
andCommFD {b1 = True} {b2 = False} = Refl
andCommFD {b1 = True} {b2 = True} = Refl

export
swapOr : Suffix (b1 || b2) xs ys -> Suffix (b2 || b1) xs ys
swapOr x = replace {p = \x => Suffix x xs ys} orCommFD x

export
swapAnd : Suffix (b1 && b2) xs ys -> Suffix (b2 && b1) xs ys
swapAnd x = replace {p = \x => Suffix x xs ys} andCommFD x

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


infixr 3 ~>,~?>,~~>

infixl 3 <~

||| Operator alias for `trans`.
public export %inline
(~>) : Suffix b1 xs ys -> Suffix b2 ys cs -> Suffix (b1 || b2) xs cs
(~>) = trans

||| Flipped version of `(~>)`.
public export %inline
(<~) : Suffix b1 ys cs -> Suffix b2 xs ys -> Suffix (b1 || b2) xs cs
x <~ y = swapOr $ trans y x

||| Operator alias for `trans` where the result is always non-strict
||| suffix dominates.
public export %inline
(~?>) : Suffix b1 xs ys -> Suffix b2 ys cs -> Suffix False xs cs
(~?>) x y = weaken $ trans x y

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

--------------------------------------------------------------------------------
--         Lexing
--------------------------------------------------------------------------------

public export
data SuffixRes : Bool -> (t : Type) -> List t -> (a : Type) -> Type where
  Succ :
       {0 t,a : Type}
    -> {0 ts : List t}
    -> (val : a)
    -> (xs : List t)
    -> {auto p : Suffix b xs ts}
    -> SuffixRes b t ts a

  Fail : SuffixRes b t ts a

namespace SuffixRes
  public export
  (~>) :
       SuffixRes b1 t ts a
    -> Suffix b2 ts ys
    -> SuffixRes (b1 || b2) t ys a
  (~>) (Succ val xs) y = Succ val xs @{%search ~> y}
  (~>)  Fail         _ = Fail

public export
Functor (SuffixRes b t ts) where
  map f (Succ v xs) = Succ (f v) xs
  map _ Fail        = Fail

public export
0 AutoTok : Bool -> (t,a : Type) -> Type
AutoTok s t a =
     {0 b      : Bool}
  -> {0 orig   : List t}
  -> (xs       : List t)
  -> {auto  su : Suffix b xs orig}
  -> SuffixRes (s || b) t orig a

public export
octDigit : Char -> Nat
octDigit '0' = 0
octDigit '1' = 1
octDigit '2' = 2
octDigit '3' = 3
octDigit '4' = 4
octDigit '5' = 5
octDigit '6' = 6
octDigit _   = 7

public export
digit : Char -> Nat
digit '8' = 8
digit '9' = 9
digit c   = octDigit c

public export
hexDigit : Char -> Nat
hexDigit c = case toLower c of
  'a' => 10
  'b' => 11
  'c' => 12
  'd' => 13
  'e' => 14
  'f' => 15
  c   => digit c

public export
ontoDec : (n : Nat) -> AutoTok False Char Nat
ontoDec n (x :: xs) =
  if isDigit x then ontoDec (n*10 + digit x) xs else Succ n (x::xs)
ontoDec n []        = Succ n []

public export
nat : AutoTok True Char Nat
nat (x :: xs) = if isDigit x then ontoDec (digit x) xs else Fail
nat []        = Fail

public export
ontoOct : (n : Nat) -> AutoTok False Char Nat
ontoOct n (x :: xs) =
  if isOctDigit x then ontoOct (n*8 + octDigit x) xs else Succ n (x::xs)
ontoOct n []        = Succ n []

public export
octNat : AutoTok True Char Nat
octNat ('0' :: 'o' :: x :: xs) =
  if isOctDigit x then ontoOct (octDigit x) xs else Fail
octNat _                       = Fail

public export
ontoHex : (n : Nat) -> AutoTok False Char Nat
ontoHex n (x :: xs) =
  if isHexDigit x then ontoHex (n*16 + hexDigit x) xs else Succ n (x::xs)
ontoHex n []        = Succ n []

public export
hexNat : AutoTok True Char Nat
hexNat ('0' :: 'x' :: x :: xs) =
  if isHexDigit x then ontoHex (hexDigit x) xs else Fail
hexNat _                       = Fail

public export
int : AutoTok True Char Integer
int ('-' :: xs) = map (negate . cast) (nat {b} xs)
int xs          = map cast (nat {b} xs)

public export
intPlus : AutoTok True Char Integer
intPlus ('+' :: xs) = int {b} xs
intPlus xs          = int {b} xs
