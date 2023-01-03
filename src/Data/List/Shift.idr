module Data.List.Shift

import Data.Bool
import Data.List
import Data.List.Suffix
import Text.Lex.Bounded

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
||| @ sa     : the current snoclist
||| @ as     : the current list
||| @ giro   : the initial snoclist
||| @ orig   : the initial list
public export
data Shift :
     (strict : Bool)
  -> (sa     : SnocList a)
  -> (as     : List a)
  -> (giro   : SnocList a)
  -> (orig   : List a)
  -> Type where

  ||| Doing nothing results in a non-strict `Shift`
  Same : Shift False sa as sa as

  ||| We arrive at a new result by shifting one more value.
  SH   : Shift b1 sa (h :: t) sx xs -> Shift b2 (sa :< h) t sx xs

export %inline
sh : Shift b sa (h :: t) sx xs -> Shift True (sa :< h) t sx xs
sh = SH

export %inline
sh1 : Shift True (sa :< x) t sa (x :: t)
sh1 = SH Same

export %inline
sh2 : Shift True (sa :< x :< y) t sa (x :: y :: t)
sh2 = SH sh1

export %inline
sh3 : Shift True (sa :< x :< y :< z) t sa (x :: y :: z :: t)
sh3 = SH sh2

export
weaken : Shift b sa as sx xs -> Shift False sa as sx xs
weaken Same   = Same
weaken (SH x) = SH x

export
suffix : Shift b sa as sx xs -> Suffix b as xs
suffix Same   = Same
suffix (SH x) = weakenS $ consLeft $ suffix x

export
and1 : {b1,b2 : Bool} -> Shift b1 sa as sx xs -> Shift (b1 && b2) sa as sx xs
and1 {b1 = True}  {b2 = True}  x = x
and1 {b1 = True}  {b2 = False} x = weaken x
and1 {b1 = False}              x = x

export
or1 : {b1,b2 : Bool} -> Shift (b1 || b2) sa as sb bs -> Shift b1 sa as sb bs
or1 {b1 = True}               x = x
or1 {b1 = False} {b2 = True}  x = weaken x
or1 {b1 = False} {b2 = False} x = x

export
and2 : {b1,b2 : Bool} -> Shift b1 sa as sx xs -> Shift (b2 && b1) sa as sx xs
and2 {b1 = True}  {b2 = True}  x = x
and2 {b1 = True}  {b2 = False} x = weaken x
and2 {b1 = False} {b2 = True}  x = x
and2 {b1 = False} {b2 = False} x = x

export
or2 : {b1,b2 : Bool} -> Shift (b1 || b2) sa as sb bs -> Shift b2 sa as sb bs
or2 {b1 = True}  {b2 = True}  x = x
or2 {b1 = True}  {b2 = False} x = weaken x
or2 {b1 = False}              x = x

export
sleft : Shift b sa (h :: bs) sc cs -> Shift True (sa :< h) bs sc cs
sleft Same   = SH Same
sleft (SH x) = SH (sleft x)

export
trans : Shift b1 sa as sb bs -> Shift b2 sb bs sc cs -> Shift (b1 || b2) sa as sc cs
trans Same y        = y
trans (SH x) Same   = SH x
trans (SH x) (SH y) = SH $ trans x (sleft y)

export
swapOr : {b1,b2 : Bool} -> Shift (b1 || b2) sa as sx xs -> Shift (b2 || b1) sa as sx xs
swapOr x = rewrite orCommutative b2 b1 in x

export
swapAnd : {b1,b2 : Bool} -> Shift (b1 && b2) sa as sx xs -> Shift (b2 && b1) sa as sx xs
swapAnd x = rewrite andCommutative b2 b1 in x
