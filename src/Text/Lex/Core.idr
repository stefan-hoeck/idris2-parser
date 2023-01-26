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
import public Data.Vect
import public Text.Lex.ShiftRes
import public Text.Lex.SuffixRes
import public Data.SnocList
import public Text.Lex.Bounded

%default total

--------------------------------------------------------------------------------
--          Recognise
--------------------------------------------------------------------------------

public export
data Recognise : (strict : Bool) -> Type -> Type where
  Lift  : Shifter b t -> Recognise b t
  (<+>) : Recognise b1 t -> Recognise b2 t -> Recognise (b1 || b2) t
  (<|>) : Recognise b1 t -> Lazy (Recognise b2 t) -> Recognise (b1 && b2) t

public export %inline
autoLift : AutoShift b t -> Recognise b t
autoLift f = Lift $ \st,ts => rewrite sym (orFalseNeutral b) in f ts @{Same}

||| Alias for `Recognise True Char`.
public export
0 Lexer : Type
Lexer = Recognise True Char

public export
run : Recognise b t -> Shifter b t
run (Lift f)  st ts = f st ts
run (x <+> y) st ts = case run x st ts of
  Succ {pre = st2} ts2 @{p2} => swapOr $ run y st2 ts2 ~> p2
  Stop                       => Stop
run (x <|> y) st ts = run x st ts <|> run y st ts

||| The empty lexer, which never consumes any input.
export %inline
empty : Recognise False t
empty = Lift $ \sc,cs => Succ cs

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
  Succ {} => Succ xs
  Stop    => Stop

||| Negative look-ahead. Does not consume any input.
export
reject : Recognise b t -> Recognise False t
reject r = Lift $ \sx,xs => case run r sx xs of
  Stop    => Succ xs
  Succ {} => Stop

export %inline
seqSame : Recognise b t -> Recognise b t -> Recognise b t
seqSame x y = rewrite sym (orSameNeutral b) in x <+> y

export %inline
altSame : Recognise b t -> Recognise b t -> Recognise b t
altSame x y = rewrite sym (andSameNeutral b) in x <|> y

||| The lexer which always fails.
export
stop : Recognise True t
stop = Lift stop

manyOnto :
     Recognise True t
  -> (st    : SnocList t)
  -> (ts    : List t)
  -> (0 acc : SuffixAcc ts)
  -> ShiftRes False st ts
manyOnto f st ts (SA rec) = case run f st ts of
  Succ {pre = st2} ts2 @{p2} =>
    let 0 x := suffix p2 in manyOnto f st2 ts2 rec ~?> p2
  Stop                      => Succ ts

||| Runs the given lexer zero or more times.
export
many : Recognise True t -> Recognise False t
many r = Lift $ \sx,xs => manyOnto r sx xs suffixAcc

||| Runs the given lexer several times, but at least once.
export
some : Recognise True t -> Recognise True t
some r = r <+> many r

||| Lexer consuming one item if it fulfills the given predicate.
export %inline
pred : (t -> Bool) -> Recognise True t
pred f = autoLift $ one f

||| Recogniser consuming items while they fulfill the given predicate.
||| This is an optimized version of `many . pred`.
export %inline
preds0 : (t -> Bool) -> Recognise False t
preds0 f = autoLift $ takeWhile f

||| Lexer consuming items while they fulfill the given predicate.
||| This is an optimized version of `some . pred`.
export %inline
preds : (t -> Bool) -> Recognise True t
preds f = autoLift $ takeWhile1 f

cmap : (a -> Recognise c t) -> (xs : List a) -> Shifter False t
cmap f (x :: xs) st ts = case run (f x) st ts of
   Succ {pre = st2} ts2 @{p2} => cmap f xs st2 ts2 ~?> p2
   Stop                      => Stop
cmap f [] sc cs = Succ cs

export
concatMap :
     (a -> Recognise c t)
  -> (xs : List a)
  -> {auto 0 prf : NonEmpty xs}
  -> Recognise c t
concatMap f (x :: [])          = f x
concatMap f (x :: xs@(_ :: _)) = seqSame (f x) (concatMap f xs)

export
choiceMap : Foldable t => (a -> Recognise c b) -> t a -> Recognise c b
choiceMap f = foldl (\v,e => altSame v $ f e) (Lift $ \_,_ => Stop)

export %inline
choice : Foldable t => t (Recognise c b) -> Recognise c b
choice = choiceMap id

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
  res   : Bounded a
  rem   : List Char
  prf   : Suffix True rem cs

export
step :
     (l, c : Nat)
  -> Lexer
  -> (SnocList Char -> a)
  -> (cs : List Char)
  -> Maybe (Step a cs)
step l c x f cs = case run x [<] cs of
  Succ {pre = sc} cs2 @{p} =>
    let (l2,c2) := lineCol l c 0 sc
     in Just $ ST l2 c2 (bounded (f sc) l c l2 c2) cs2 (suffix p)
  Stop         => Nothing

export
first : (l, c : Nat) -> TokenMap a -> (cs : List Char) -> Maybe (Step a cs)
first l c ((f,g) :: ps) cs = step l c f g cs <|> first l c ps cs
first _ _ []            _  = Nothing
