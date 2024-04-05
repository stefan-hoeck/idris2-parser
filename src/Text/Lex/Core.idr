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
import public Text.Bounds
import public Text.ParseError
import public Text.Lex.Shift

%default total

--------------------------------------------------------------------------------
--          Recognise
--------------------------------------------------------------------------------

export infixl 8 <++>

public export
data Recognise : (strict : Bool) -> Type where
  Lift      : Shifter b -> Recognise b
  (<+>)     : Recognise b1 -> Recognise b2 -> Recognise (b1 || b2)
  (<++>)    : Recognise True -> Inf (Recognise b) -> Recognise True
  (<|>)     : Recognise b1 -> Lazy (Recognise b2) -> Recognise (b1 && b2)

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
swapOr : {0 x,y : _} -> Recognise (x || y) -> Recognise (y || x)
swapOr = swapOr (\k => Recognise k)

public export %inline
orSame : {0 x : _} -> Recognise (x || x) -> Recognise x
orSame = orSame (\k => Recognise k)

public export %inline
orTrue : {0 x : _} -> Recognise (x || True) -> Recognise True
orTrue = orTrue (\k => Recognise k)

public export %inline
orFalse : {0 x : _} -> Recognise (x || False) -> Recognise x
orFalse = orFalse (\k => Recognise k)

public export %inline
swapAnd : {0 x,y : _} -> Recognise (x && y) -> Recognise (y && x)
swapAnd = swapAnd (\k => Recognise k)

public export %inline
andSame : {0 x : _} -> Recognise (x && x) -> Recognise x
andSame = andSame (\k => Recognise k)

public export %inline
andTrue : {0 x : _} -> Recognise (x && True) -> Recognise x
andTrue = andTrue (\k => Recognise k)

public export %inline
andFalse : {0 x : _} -> Recognise (x && False) -> Recognise False
andFalse = andFalse (\k => Recognise k)

--------------------------------------------------------------------------------
--          Core Lexers
--------------------------------------------------------------------------------

public export %inline
autoLift : AutoShift b -> Recognise b
autoLift f = Lift $ \st,ts => orFalse $ f ts @{Same}

||| Alias for `Recognise True Char`.
public export
0 Lexer : Type
Lexer = Recognise True

public export
run :
     Recognise b
  -> (st : SnocList Char)
  -> (ts : List Char)
  -> (0 acc : SuffixAcc ts)
  -> ShiftRes b st ts
run (Lift f)  st ts _ = f st ts
run (x <+> y) st ts a@(SA r) = case run x st ts a of
  Succ {pre} ts2 @{p} => case p of
    Same => run y pre ts a
    SH q =>
      let su := suffix {b = True} (SH q)
       in swapOr $ run y pre ts2 r `trans` SH q
  Stop start errEnd r        => Stop start errEnd r
run (x <++> y) st ts a@(SA r) = case run x st ts a of
  Succ {pre} ts2 @{p} =>
    let su := suffix {b = True} p
     in swapOr $ run y pre ts2 r `trans` p
  Stop start errEnd r        => Stop start errEnd r
run (x <|> y) st ts a = run x st ts a <|> run y st ts a

||| Lexer succeeding always without consuming input
public export %inline
empty : Recognise False
empty = Lift $ \sc,cs => Succ cs

||| Renders the given lexer optional.
public export %inline
opt : Recognise True -> Recognise False
opt l = l <|> empty

||| Positive look-ahead. Does not consume any input.
public export
expect : Recognise b -> Recognise False
expect r = Lift $ \sc,cs => case run r sc cs suffixAcc of
  Succ _     => Succ cs
  Stop x y z => Stop x y z

||| Negative look-ahead. Does not consume any input.
public export
reject : Recognise b -> Recognise False
reject r = Lift $ \sc,cs => case run r sc cs suffixAcc of
  Stop {} => Succ cs
  Succ {} => weaken $ fail sc cs

public export %inline
seqSame : Recognise b -> Recognise b -> Recognise b
seqSame x y = orSame $ x <+> y

public export %inline
altSame : Recognise b -> Recognise b -> Recognise b
altSame x y =  andSame $ x <|> y

||| The lexer which always fails.
public export
fail : Recognise True
fail = Lift fail

||| Runs the given lexer zero or more times.
public export
many : Recognise True -> Recognise False

||| Runs the given lexer several times, but at least once.
public export
some : Recognise True -> Recognise True

many r = opt (some r)

some r = r <++> many r

||| Lexer consuming one item if it fulfills the given predicate.
public export %inline
pred : (Char -> Bool) -> Recognise True
pred f = autoLift $ one f

||| Lexer consuming items while they fulfill the given predicate.
||| This is an optimized version of `some . pred`.
public export %inline
preds : (Char -> Bool) -> Recognise True
preds f = autoLift $ takeWhile1 f

||| Recogniser consuming items while they fulfill the given predicate.
||| This is an optimized version of `many . pred`.
public export %inline
preds0 : (Char -> Bool) -> Recognise False
preds0 = opt . preds

public export
concatMap :
     (a -> Recognise c)
  -> (xs : List a)
  -> {auto 0 prf : NonEmpty xs}
  -> Recognise c
concatMap f (x :: [])          = f x
concatMap f (x :: xs@(_ :: _)) = seqSame (f x) (concatMap f xs)

public export %inline
choiceMap : Foldable t => (a -> Recognise True) -> t a -> Recognise True
choiceMap f = foldl (\v,e => altSame v $ f e) fail

public export %inline
choice : Foldable t => t (Recognise True) -> Recognise True
choice = choiceMap id

--------------------------------------------------------------------------------
--          Lex
--------------------------------------------------------------------------------

public export
0 TokenMap : (tokenType : Type) -> Type
TokenMap tt = List (Recognise True, SnocList Char -> tt)

public export %inline
step : Recognise True -> (SnocList Char -> a) -> Tok True e a
step x f cs = suffix f $ run x [<] cs suffixAcc

public export
first : (ps : TokenMap a) -> {auto 0 prf : NonEmpty ps} -> Tok True e a
first ((f,g) :: [])         cs = step f g cs
first ((f,g) :: t@(_ :: _)) cs = step f g cs <|> first t cs
