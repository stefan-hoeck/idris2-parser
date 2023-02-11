||| A simple library of lexers and their combinators. A `Lexer` is
||| just a (dependent) function, which is guaranteed to consume a non-empty
||| prefix of the input list of characters.
|||
||| As such, high-performance lexers can be written manually, while
||| many convenient combinators exist for less performance-critical
||| applications.
module Text.Lex.Core

import Data.Bool.Rewrite
import public Data.List
import public Data.SnocList
import public Data.Vect
import public Text.Bounded
import public Text.ParseError
import public Text.ShiftRes

%default total

--------------------------------------------------------------------------------
--          Recognise
--------------------------------------------------------------------------------

infixl 8 <++>

public export
data Recognise : (strict : Bool) -> Type -> Type where
  Lift      : Shifter b t -> Recognise b t
  (<+>)     : Recognise b1 t -> Recognise b2 t -> Recognise (b1 || b2) t
  (<++>)    : Recognise True t -> Inf (Recognise b t) -> Recognise True t
  (<|>)     : Recognise b1 t -> Lazy (Recognise b2 t) -> Recognise (b1 && b2) t

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
swapOr : {0 x,y : _} -> Recognise (x || y) t -> Recognise (y || x) t
swapOr = swapOr (\k => Recognise k t)

public export %inline
orSame : {0 x : _} -> Recognise (x || x) t -> Recognise x t
orSame = orSame (\k => Recognise k t)

public export %inline
orTrue : {0 x : _} -> Recognise (x || True) t -> Recognise True t
orTrue = orTrue (\k => Recognise k t)

public export %inline
orFalse : {0 x : _} -> Recognise (x || False) t -> Recognise x t
orFalse = orFalse (\k => Recognise k t)

public export %inline
swapAnd : {0 x,y : _} -> Recognise (x && y) t -> Recognise (y && x) t
swapAnd = swapAnd (\k => Recognise k t)

public export %inline
andSame : {0 x : _} -> Recognise (x && x) t -> Recognise x t
andSame = andSame (\k => Recognise k t)

public export %inline
andTrue : {0 x : _} -> Recognise (x && True) t -> Recognise x t
andTrue = andTrue (\k => Recognise k t)

public export %inline
andFalse : {0 x : _} -> Recognise (x && False) t -> Recognise False t
andFalse = andFalse (\k => Recognise k t)

--------------------------------------------------------------------------------
--          Core Lexers
--------------------------------------------------------------------------------

public export %inline
autoLift : AutoShift b t -> Recognise b t
autoLift f = Lift $ \st,ts => orFalse $ f ts @{Same}

||| Alias for `Recognise True Char`.
public export
0 Lexer : Type
Lexer = Recognise True Char

public export
run :
     Recognise b t
  -> (st : SnocList t)
  -> (ts : List t)
  -> (0 acc : SuffixAcc ts)
  -> ShiftRes b t st ts
run (Lift f)  st ts _ = f st ts
run (x <+> y) st ts a@(SA r) = case run x st ts a of
  Succ {pre} ts2 @{p} => case p of
    Same => run y pre ts a
    SH q =>
      let su := suffix {b = True} (SH q)
       in swapOr $ run y pre ts2 r ~> SH q
  Stop start errEnd r        => Stop start errEnd r
run (x <++> y) st ts a@(SA r) = case run x st ts a of
  Succ {pre} ts2 @{p} =>
    let su := suffix {b = True} p
     in swapOr $ run y pre ts2 r ~> p
  Stop start errEnd r        => Stop start errEnd r
run (x <|> y) st ts a = run x st ts a <|> run y st ts a


||| Lexer succeeding always without consuming input
public export %inline
empty : Recognise False t
empty = Lift $ \sc,cs => Succ cs

||| Renders the given lexer optional.
public export %inline
opt : Recognise True t -> Recognise False t
opt l = l <|> empty

||| Positive look-ahead. Does not consume any input.
public export
expect : Recognise b t -> Recognise False t
expect r = Lift $ \sc,cs => case run r sc cs suffixAcc of
  Succ _     => Succ cs
  Stop x y z => Stop x y z

||| Negative look-ahead. Does not consume any input.
public export
reject : Recognise b t -> Recognise False t
reject r = Lift $ \sc,cs => case run r sc cs suffixAcc of
  Stop {} => Succ cs
  Succ {} => weaken $ fail sc cs

public export %inline
seqSame : Recognise b t -> Recognise b t -> Recognise b t
seqSame x y = orSame $ x <+> y

public export %inline
altSame : Recognise b t -> Recognise b t -> Recognise b t
altSame x y =  andSame $ x <|> y

||| The lexer which always fails.
public export
fail : Recognise True t
fail = Lift fail

||| Runs the given lexer zero or more times.
public export
many : Recognise True t -> Recognise False t

||| Runs the given lexer several times, but at least once.
public export
some : Recognise True t -> Recognise True t

many r = opt (some r)

some r = r <++> many r

||| Lexer consuming one item if it fulfills the given predicate.
public export %inline
pred : (t -> Bool) -> Recognise True t
pred f = autoLift $ one f

||| Lexer consuming items while they fulfill the given predicate.
||| This is an optimized version of `some . pred`.
public export %inline
preds : (t -> Bool) -> Recognise True t
preds f = autoLift $ takeWhile1 f

||| Recogniser consuming items while they fulfill the given predicate.
||| This is an optimized version of `many . pred`.
public export %inline
preds0 : (t -> Bool) -> Recognise False t
preds0 = opt . preds

public export
concatMap :
     (a -> Recognise c t)
  -> (xs : List a)
  -> {auto 0 prf : NonEmpty xs}
  -> Recognise c t
concatMap f (x :: [])          = f x
concatMap f (x :: xs@(_ :: _)) = seqSame (f x) (concatMap f xs)

public export %inline
choiceMap : Foldable t => (a -> Recognise True b) -> t a -> Recognise True b
choiceMap f = foldl (\v,e => altSame v $ f e) fail

public export %inline
choice : Foldable t => t (Recognise True b) -> Recognise True b
choice = choiceMap id

--------------------------------------------------------------------------------
--          Lex
--------------------------------------------------------------------------------

public export
0 TokenMap : (charType, tokenType : Type) -> Type
TokenMap ct tt = List (Recognise True ct, SnocList ct -> tt)

public export %inline
step : Recognise True t -> (SnocList t -> a) -> Tok t a
step x f cs = suffix f $ run x [<] cs suffixAcc

public export
first : (ps : TokenMap t a) -> {auto 0 prf : NonEmpty ps} -> Tok t a
first ((f,g) :: [])         cs = step f g cs
first ((f,g) :: t@(_ :: _)) cs = step f g cs <|> first t cs
