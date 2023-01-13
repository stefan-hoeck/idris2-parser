module Data.List.Tail

import Data.List.Suffix

%default total

public export
data Tail : (strict : Bool) -> (cs,cs' : List a) -> Type where
  Same   : Tail False cs cs
  Uncons : Tail b (h :: t) cs -> Tail b2 t cs

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
