module Data.List.Shift

import Data.Bool
import Data.List
import Data.List.Suffix
import Data.List.Tail
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
  [search strict as giro orig]

  ||| Doing nothing results in a non-strict `Shift`
  Same : Shift False sa as sa as

  ||| We arrive at a new result by shifting one more value.
  SH   : Shift b1 sa (h :: t) sx xs -> Shift b2 (sa :< h) t sx xs

export %inline
sh : Shift b sa (h :: t) sx xs -> Shift True (sa :< h) t sx xs
sh = SH

public export
0 SHL : List t -> SnocList t -> List t -> Type 
SHL ts sa as = Shift (isCons ts) (sa <>< ts) as sa (ts ++ as)

export %inline
sh1 : SHL [x] st ts
sh1 = SH Same

export %inline
sh2 : SHL [x,y] st ts 
sh2 = SH sh1

export %inline
sh3 : SHL [x,y,z] st ts
sh3 = SH sh2

export %inline
sh4 : SHL [w,x,y,z] st ts
sh4 = SH sh3

export %inline
sh5 : SHL [v,w,x,y,z] st ts
sh5 = SH sh4

export %inline
sh6 : SHL [u,v,w,x,y,z] st ts
sh6 = SH sh5

export %inline
sh7 : SHL [t,u,v,w,x,y,z] st ts
sh7 = SH sh6

export %inline
sh8 : SHL [s,t,u,v,w,x,y,z] st ts
sh8 = SH sh7

export %inline
sh9 : SHL [r,s,t,u,v,w,x,y,z] st ts
sh9 = SH sh8

export %inline
sh10 : SHL [q,r,s,t,u,v,w,x,y,z] st ts
sh10 = SH sh9

export
weaken : Shift b sa as sx xs -> Shift False sa as sx xs
weaken Same   = Same
weaken (SH x) = SH x

export
weakens : Shift True sa as sx xs -> Shift b sa as sx xs
weakens (SH x) = SH x
weakens Same impossible

export
toTail : Shift b sa as sx xs -> Tail b as xs
toTail Same   = Same
toTail (SH x) = Uncons $ toTail x

export
toSuffix : Shift b sa as sx xs -> Suffix b as xs
toSuffix s = suffix $ toTail s

export %inline
toNat : Shift b sa as sx xs -> Nat
toNat s = tailToNat $ toTail s

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

--------------------------------------------------------------------------------
--          Rec
--------------------------------------------------------------------------------

||| Result of running a lexer once: The lexer either stops, when
||| it can no longer consume any characters, or it shifts some characters
||| from the head of the list of remaining characters to the tail of the
||| snoclist or already recognised characters.
|||
||| @ strict : `True` if we can proof that the lexer recognised at least
|||            one character
||| @ st     : the initial snoclist of already recognised characters
||| @ ts     : the initial list of remaining characters
public export
data Rec :
     (strict : Bool)
  -> (st     : SnocList t)
  -> (ts     : List t)
  -> Type where

  Stop : Rec s st ts

  Res :  {0 st      : SnocList t}
      -> {0 ts      : List t}
      -> {pre       : SnocList t}
      -> (post      : List t)
      -> {auto 0 sh : Shift b pre post st ts}
      -> Rec b st ts

||| This is the identity at runtime
export
mapPrf :
     {0 t     : Type}
  -> {0 sa,sb : SnocList t}
  -> {0 as,bs : List t}
  -> (0 f :
          {st : SnocList t}
       -> {ts : List t}
       -> Shift b1 st ts sa as
       -> Shift b2 st ts sb bs
     )
  -> Rec b1 sa as
  -> Rec b2 sb bs
mapPrf f Stop              = Stop
mapPrf f (Res toks @{prf}) = Res toks @{f prf}

namespace Rec
  export %inline
  weaken : Rec b1 sa as -> Rec False sa as
  weaken = mapPrf weaken

  export %inline
  weakens : Rec True sa as -> Rec b sa as
  weakens = mapPrf weakens

export %inline
(~>) : Rec s1 sa as -> (0 p : Shift s2 sa as sb bs) -> Rec (s2 || s1) sb bs
r ~> p = mapPrf (\q => swapOr $ trans q p) r

export %inline
(~?>) : Rec s1 sa as -> (0 p : Shift s2 sa as sb bs) -> Rec False sb bs
r ~?> p = mapPrf (\q => weaken $ trans q p) r

namespace Rec
  export
  (<|>) : Rec b1 sx xs -> Lazy (Rec b2 sx xs) -> Rec (b1 && b2) sx xs
  (<|>) r@(Res _) _  = mapPrf and1 r
  (<|>) Stop      r  = mapPrf and2 r

--------------------------------------------------------------------------------
--          Shifters
--------------------------------------------------------------------------------

||| A `Shifter` is a function that moves items from the head of a list
||| to the tail of a snoclist.
|||
||| A lexer is just a fancy wrapper around a `Shifter`, and *running* a
||| lexer (via function `run`) leads to the underlying `Shifter`.
public export
0 Shifter : (b : Bool) -> Type -> Type
Shifter b t = (st : SnocList t) -> (ts : List t) -> Rec b st ts

||| Shifter that recognises the empty String
public export
eoi : Shifter False t
eoi _ [] = Res []
eoi _ _  = Stop

||| Shifter that always fails
public export
stop : Shifter True t
stop _ _ = Stop

public export
0 AutoShift : Bool -> Type -> Type
AutoShift s a =
     {0 b       : Bool}
  -> {0 giro    : SnocList a}
  -> {0 orig    : List a}
  -> {pre       : SnocList a}
  -> (post      : List a)
  -> {auto 0 sh : Shift b pre post giro orig}
  -> Rec (s || b) giro orig

||| A shifter that doesn't move anything.
public export
same : AutoShift False a
same post = Res post

||| A shifter that moves exactly one value
public export
tail : AutoShift True a
tail (x :: xs) = Res xs
tail []        = Stop

||| A shifter that moves exactly one value, if
||| it fulfills the given predicate.
public export
one : (t -> Bool) -> AutoShift True t
one f (x :: xs) = if f x then Res xs else Stop
one _ []        = Stop

||| A shifter that moves items while the given predicate returns
||| `True`
public export
takeWhile : (a -> Bool) -> AutoShift False a
takeWhile f (x :: xs) = if f x then takeWhile f xs else Res (x::xs)
takeWhile f []        = Res []

||| A strict version of `takeWhile`, which moves at least one item.
public export
takeWhile1 : (a -> Bool) -> AutoShift True a
takeWhile1 f (x :: xs) = if f x then takeWhile f xs else Stop
takeWhile1 f []        = Stop

||| A shifter that moves items while the give predicate returns
||| `False`
public export
takeUntil : (t -> Bool) -> AutoShift False t
takeUntil f (x :: xs) = if f x then Res (x::xs) else takeUntil f xs
takeUntil f []        = Res []

||| A strict version of `takeUntil`, which moves at least one item.
public export
takeUntil1 : (t -> Bool) -> AutoShift True t
takeUntil1 f (x :: xs) = if f x then Stop else takeUntil f xs
takeUntil1 f []        = Stop

||| A shifter that moves digits.
public export
digits : AutoShift False Char
digits (x :: xs) = if isDigit x then digits xs else Res(x::xs)
digits []        = Res []

||| A strict version of `digits`.
public export
digits1 : AutoShift True Char
digits1 (x :: xs) = if isDigit x then digits xs else Stop
digits1 []        = Stop

||| A shifter that takes moves an integer prefix
public export
int : AutoShift True Char
int ('-' :: xs) = digits1 {b} xs
int xs          = digits1 {b} xs

||| Like `int` but also allows an optional leading `'+'` character.
public export
intPlus : AutoShift True Char
intPlus ('+' :: xs) = digits1 {b} xs
intPlus xs          = int {b} xs

dot,rest,digs,exp : AutoShift False Char
exp ('e' :: xs) = weakens $ intPlus {b} xs
exp ('E' :: xs) = weakens $ intPlus {b} xs
exp xs          = Res xs

dot (x :: xs) = if isDigit x then dot xs else exp (x::xs)
dot []        = Res []

rest ('.' :: x :: xs) = if isDigit x then dot xs else Stop
rest xs               = exp xs

digs (x :: xs) = if isDigit x then digs xs else rest (x::xs)
digs []        = Res []

digs0 : AutoShift True Char
digs0 ('0' :: xs) = rest xs
digs0 (x :: xs)   = if isDigit x then digs xs else Stop
digs0 []          = Stop

||| A shifter for recognizing JSON numbers
public export
number : AutoShift True Char
number ('-' :: xs) = digs0 {b} xs
number xs          = digs0 {b} xs

public export
take : (n : Nat) -> AutoShift (isSucc n) a
take (S k) (x::xs) = rewrite sym (orTrueTrue _) in take k xs
take 0     xs      = Res xs
take (S k) []      = Stop

public export
exact : Eq t => List t -> AutoShift True t
exact (v :: []) (x :: xs) = if v == x then Res xs else Stop
exact (v :: vs) (x :: xs) = if v == x then exact {b} vs xs else Stop
exact _         _         = Stop

str : AutoShift True Char
str ('"'       :: xs) = Res xs
str ('\\' :: x :: xs) = str {b} xs
str (x         :: xs) = str {b} xs
str []                = Stop

public export
string : AutoShift True Char
string ('"' :: xs) = str {b} xs
string _           = Stop
