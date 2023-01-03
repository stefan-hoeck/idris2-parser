||| A simple library of lexers and their combinators. A `Lexer` is
||| just a (dependent) function, which is guaranteed to consume a non-empty
||| prefix of the input list of characters.
|||
||| As such, high-performance lexers can be written manually, while
||| many convenient combinators exist for less performance-critical
||| applications.
module Text.Lex.Core

import Data.Bool
import public Data.List
import public Data.List.Shift
import public Data.List.Suffix
import public Data.SnocList
import public Text.Lex.Bounded

%default total

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

  Res :  {0 st  : SnocList t}
      -> {0 ts  : List t}
      -> (pre   : SnocList t)
      -> (post  : List t)
      -> (0 prf : Shift b pre post st ts)
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
mapPrf f (Res sc toks prf) = Res sc toks (f prf)

export %inline
(~>) : Rec s1 sa as -> (0 p : Shift s2 sa as sb bs) -> Rec (s2 || s1) sb bs
r ~> p = mapPrf (\q => swapOr $ trans q p) r

export %inline
(~?>) : Rec s1 sa as -> (0 p : Shift s2 sa as sb bs) -> Rec False sb bs
r ~?> p = mapPrf (\q => weaken $ trans q p) r

namespace Rec
  export
  (<|>) : Rec b1 sx xs -> Lazy (Rec b2 sx xs) -> Rec (b1 && b2) sx xs
  (<|>) r@(Res _ _ _) _  = mapPrf and1 r
  (<|>) Stop          r  = mapPrf and2 r

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

||| A shifter that doesn't move anything.
public export
same : Shifter False t
same st ts = Res st ts Same

||| A shifter that moves exactly one value
public export
head : Shifter True t
head st (x :: xs) = Res (st :< x) xs %search
head _  []        = Stop

||| A shifter that moves exactly one value, if
||| it fulfills the given predicate.
public export
one : (t -> Bool) -> Shifter True t
one f st (x :: xs) =
  if f x then Res (st :< x) xs %search else Stop
one _ _  []        = Stop

||| A shifter that moves exactly `n` values.
public export
take : (n : Nat) -> Shifter (isSucc n) t
take 0     st ts        = Res st ts Same
take (S k) st (x :: xs) = take k (st :< x) xs ~> sh1
take (S k) st []        = Stop

||| A shifter that moves items while the give predicate returns
||| `True`
public export
takeWhile : (t -> Bool) -> Shifter False t
takeWhile f st (x :: xs) =
  if f x then takeWhile f (st :< x) xs ~?> sh1 else Res st (x :: xs) Same
takeWhile f st []        = Res st [] Same

||| A strict version of `takeWhile`, which moves at least one item.
public export
takeWhile1 : (t -> Bool) -> Shifter True t
takeWhile1 f st (x :: xs) =
  if f x then takeWhile f (st :< x) xs ~> sh1 else Stop
takeWhile1 f st []        = Stop

||| A shifter that moves items while the give predicate returns
||| `False`
public export
takeUntil : (t -> Bool) -> Shifter False t
takeUntil f st (x :: xs) =
  if f x then Res st (x :: xs) Same else takeUntil f (st :< x) xs ~?> sh1
takeUntil f st []        = Res st [] Same

||| A strict version of `takeUntil`, which moves at least one item.
public export
takeUntil1 : (t -> Bool) -> Shifter True t
takeUntil1 f st (x :: xs) =
  if f x then Stop else takeUntil f (st :< x) xs ~> sh1
takeUntil1 f st []        = Stop

namespace Shifter

  ||| Shifter that recognises the empty String
  public export
  eoi : Shifter False t
  eoi sc [] = Res sc [] Same
  eoi _  _  = Stop

  ||| Shifter that always fails
  public export
  stop : Shifter True t
  stop _ _ = Stop


--------------------------------------------------------------------------------
--          Recognise
--------------------------------------------------------------------------------

public export
data Recognise : (strict : Bool) -> Type -> Type where
  Lift  : Shifter b t -> Recognise b t
  (<+>) : Recognise b1 t -> Recognise b2 t -> Recognise (b1 || b2) t
  (<|>) : Recognise b1 t -> Lazy (Recognise b2 t) -> Recognise (b1 && b2) t

||| Alias for `Recognise True Char`.
public export
0 Lexer : Type
Lexer = Recognise True Char

public export
run : Recognise b t -> Shifter b t
run (Lift f)  st ts = f st ts
run (x <+> y) st ts = case run x st ts of
  Res st2 ts2 p2 => run y st2 ts2 ~> p2
  Stop           => Stop
run (x <|> y) st ts = run x st ts <|> run y st ts

||| The empty lexer, which never consumes any input.
export %inline
empty : Recognise False t
empty = Lift $ \sc,cs => Res sc cs Same

||| Renders the given lexer optional.
export %inline
opt : Recognise True t -> Recognise False t
opt l = l <|> empty

||| Recognises the end of input.
export %inline
eoi : Recognise False t
eoi = Lift eoi

||| Positive look-ahead. Does not consume any input.
export
expect : Recognise b t -> Recognise False t
expect r = Lift $ \sx,xs => case run r sx xs of
  Res {} => Res sx xs Same
  Stop   => Stop

||| Negative look-ahead. Does not consume any input.
export
reject : Recognise b t -> Recognise False t
reject r = Lift $ \sx,xs => case run r sx xs of
  Stop   => Res sx xs Same
  Res {} => Stop

export %inline
seqSame : Recognise b t -> Recognise b t -> Recognise b t
seqSame x y = rewrite sym (orSameNeutral b) in x <+> y

||| The lexer which always fails.
export
stop : Recognise True t
stop = Lift stop

manyOnto :
     Recognise True t
  -> (st    : SnocList t)
  -> (ts    : List t)
  -> (0 acc : SuffixAcc ts)
  -> Rec False st ts
manyOnto f st ts (Access rec) = case run f st ts of
  Res st2 ts2 p2 => manyOnto f st2 ts2 (rec ts2 $ suffix p2) ~?> p2
  Stop           => Res st ts Same

||| Runs the given lexer zero or more times.
export
many : Recognise True t -> Recognise False t
many r = Lift $ \sx,xs => manyOnto r sx xs (ssAcc _)

||| Runs the given lexer several times, but at least once.
export
some : Recognise True t -> Recognise True t
some r = r <+> many r

||| Lexer consuming one item if it fulfills the given predicate.
export %inline
pred : (t -> Bool) -> Recognise True t
pred f = Lift $ one f

||| Recogniser consuming items while they fulfill the given predicate.
||| This is an optimized version of `many . pred`.
export %inline
preds0 : (t -> Bool) -> Recognise False t
preds0 f = Lift $ takeWhile f

||| Lexer consuming items while they fulfill the given predicate.
||| This is an optimized version of `some . pred`.
export %inline
preds : (t -> Bool) -> Recognise True t
preds f = Lift $ takeWhile1 f

cmap : (a -> Recognise c t) -> (xs : List a) -> Shifter False t
cmap f (x :: xs) st ts = case run (f x) st ts of
   Res st2 ts2 p2 => cmap f xs st2 ts2 ~?> p2
   Stop           => Stop
cmap f [] sc cs = Res sc cs Same

export
concatMap :
     (a -> Recognise c t)
  -> (xs : List a)
  -> {auto 0 prf : NonEmpty xs}
  -> Recognise c t
concatMap f (x :: [])          = f x
concatMap f (x :: xs@(_ :: _)) = seqSame (f x) (concatMap f xs)

--------------------------------------------------------------------------------
--          Lex
--------------------------------------------------------------------------------

export
countNls : Nat -> SnocList Char -> Nat
countNls k (sx :< '\n') = countNls (S k) sx
countNls k (sx :< _)    = countNls k sx
countNls k [<]          = k

export
lineCol : (line,col,cur : Nat) -> SnocList Char -> (Nat,Nat)
lineCol l c cur [<]          = (l, c + cur)
lineCol l c cur (sx :< '\n') = (countNls (S l) sx, cur)
lineCol l c cur (sx :< x)    = lineCol l c (S cur) sx

public export
0 TokenMap : (tokenType : Type) -> Type
TokenMap tokenType = List (Lexer, SnocList Char -> tokenType)

public export
record Step (a : Type) (cs : List Char) where
  constructor ST
  line  : Nat
  col   : Nat
  res   : WithBounds a
  rem   : List Char
  0 prf : Suffix True rem cs

export
step :
     (l, c : Nat)
  -> Lexer
  -> (SnocList Char -> a)
  -> (cs : List Char)
  -> Maybe (Step a cs)
step l c x f cs = case run x [<] cs of
  Res sc cs2 p =>
    let (l2,c2) := lineCol l c 0 sc
        bnds    := Just $ MkBounds l c l2 c2
     in Just $ ST l2 c2 (MkBounded (f sc) bnds) cs2 (suffix p)
  Stop         => Nothing

first : (l, c : Nat) -> TokenMap a -> (cs : List Char) -> Maybe (Step a cs)
first l c ((f,g) :: ps) cs = step l c f g cs <|> first l c ps cs
first _ _ []            _  = Nothing

tokenise :
     (a -> Bool)
  -> (line, col : Nat)
  -> SnocList (WithBounds a)
  -> TokenMap a
  -> (cs    : List Char)
  -> (0 acc : SuffixAcc cs)
  -> (SnocList (WithBounds a), (Nat, Nat, List Char))
tokenise f l c sx xs cs (Access rec) = case first l c xs cs of
  Just (ST l2 c2 res rem p) => case f res.val of
    False => tokenise f l2 c2 (sx :< res) xs rem (rec rem p)
    True  => (sx, (l,c,[]))
  Nothing => (sx, (l,c,cs))

export
lexTo :
     (a -> Bool)
  -> TokenMap a
  -> String
  -> (SnocList (WithBounds a), (Nat, Nat , List Char))
lexTo f ts s = tokenise f 0 0 [<] ts (unpack s) (ssAcc _)

||| Given a mapping from lexers to token generating functions (the
||| TokenMap a) and an input string, return a list of recognised tokens,
||| and the line, column, and remainder of the input at the first point in the
||| string where there are no recognised tokens.
export %inline
lex : TokenMap a -> String -> (SnocList (WithBounds a), (Nat,Nat,List Char))
lex = lexTo (const False)
