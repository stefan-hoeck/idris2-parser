module Data.List.Tail

import Data.List
import Data.Nat
import Data.List.Suffix

%default total

public export
data Tail : (strict : Bool) -> (cs,cs' : List a) -> Type where
  Same   : Tail False cs cs
  Uncons : Tail b (h :: t) cs -> Tail b2 t cs

%builtin Natural Tail

tailCons : Tail b (y :: ys) (x :: xs) -> Tail False ys xs
tailCons Same       = Same
tailCons (Uncons z) = Uncons $ tailCons z

tailConsLeft : Tail b xs ys -> Tail b' xs (y :: ys)
tailConsLeft Same       = Uncons Same
tailConsLeft (Uncons x) = ?tailConsLeft_rhs_1

unconsRight : Tail True ys (x :: xs) -> Tail False ys xs
unconsRight (Uncons x) = tailCons x

public export
suffix : Tail b cs cs' -> Suffix b cs cs'
suffix Same       = Same
suffix (Uncons x) = weakens $ consLeft $ suffix x

public export
tailToNat : Tail b cs cs' -> Nat
tailToNat Same       = Z
tailToNat (Uncons x) = S $ tailToNat x

export
trans : Tail b1 as bs -> Tail b2 bs cs -> Tail (b1 || b2) as cs
trans Same y       = y
trans (Uncons x) t = Uncons $ trans x t

%transform "transPlus" Tail.trans x y = believe_me (tailToNat x + tailToNat y)
