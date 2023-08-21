module Data.List.Suffix.Result0

import Derive.Prelude
import Data.Nat
import Data.List.Suffix

%default total
%language ElabReflection

||| Result of consuming and converting a (possibly strict) prefix
||| of a list of tokens.
|||
||| This comes with an erased proof about the number of tokens
||| consumed. Consider using `Data.List.Suffix.Result` if you need
||| to keep track of the number of tokens consumed at runtime.
|||
||| Use this for manually writing high-performance parsers, which
||| (in the case of strict results) are guaranteed to terminate.
||| See module `Text.Parse.Manual` for
||| utilities for consuming and converting prefixes
||| of tokens, but for a nicer interface, consider using `Text.Parse.Core`
||| (at the cost of a drop in performance).
|||
||| @ strict : True if a strict prefix of the list of tokens has
|||            been consumed.
||| @ t      : the type of token consumed.
||| @ ts     : the original list of tokens
||| @ e      : the error type in case of a failure
||| @ a      : the result type
public export
data Result0 :
     (strict : Bool)
  -> (t : Type)
  -> List t
  -> (e,a : Type)
  -> Type where

  Succ0 :
       {0 b : Bool}
    -> {0 t,e,a : Type}
    -> {0 ts : List t}
    -> (val : a)
    -> (xs : List t)
    -> {auto 0 p : Suffix b xs ts}
    -> Result0 b t ts e a

  Fail0 :
       {0 b : Bool}
    -> {0 t,e,a : Type}
    -> {0 ts : List t}
    -> (err : e)
    -> Result0 b t ts e a

||| Alias for `Succ`, which takes the proof as an
||| explicit argument
public export %inline
succ : 
       {0 b : Bool}
    -> {0 t,e,a : Type}
    -> {0 ts : List t}
    -> (val : a)
    -> {xs : List t}
    -> (0 p : Suffix b xs ts)
    -> Result0 b t ts e a
succ val _ = Succ0 val xs

public export
Functor (Result0 b t ts e) where
  map f (Succ0 v xs) = Succ0 (f v) xs
  map _ (Fail0 err)  = Fail0 err

public export %inline
fromEither :
     {0 ts : List t}
  -> (xs : List t)
  -> {auto 0 p : Suffix b xs ts}
  -> Either e a
  -> Result0 b t ts e a
fromEither xs (Left x)  = Fail0 x
fromEither xs (Right x) = Succ0 x xs

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
swapOr : {0 x,y : _} -> Result0 (x || y) t ts e a -> Result0 (y || x) t ts e a
swapOr = swapOr (\k => Result0 k t ts e a)

public export %inline
orSame : {0 x : _} -> Result0 (x || x) t ts e a -> Result0 x t ts e a
orSame = orSame (\k => Result0 k t ts e a)

public export %inline
orTrue : {0 x : _} -> Result0 (x || True) t ts e a -> Result0 True t ts e a
orTrue = orTrue (\k => Result0 k t ts e a)

public export %inline
orFalse : {0 x : _} -> Result0 (x || False) t ts e a -> Result0 x t ts e a
orFalse = orFalse (\k => Result0 k t ts e a)

public export %inline
swapAnd : {0 x,y : _} -> Result0 (x && y) t ts e a -> Result0 (y && x) t ts e a
swapAnd = swapAnd (\k => Result0 k t ts e a)

public export %inline
andSame : {0 x : _} -> Result0 (x && x) t ts e a -> Result0 x t ts e a
andSame = andSame (\k => Result0 k t ts e a)

public export %inline
andTrue : {0 x : _} -> Result0 (x && True) t ts e a -> Result0 x t ts e a
andTrue = andTrue (\k => Result0 k t ts e a)

public export %inline
andFalse : {0 x : _} -> Result0 (x && False) t ts e a -> Result0 False t ts e a
andFalse = andFalse (\k => Result0 k t ts e a)

public export %inline
weaken : {0 x : _} -> Result0 x t ts e a -> Result0 False t ts e a
weaken (Succ0 val xs @{p}) = Succ0 val xs @{weaken p}
weaken (Fail0 err)         = Fail0 err

public export %inline
weakens : {0 x : _} -> Result0 True t ts e a -> Result0 x t ts e a
weakens (Succ0 val xs @{p}) = Succ0 val xs @{weakens p}
weakens (Fail0 err)         = Fail0 err

public export %inline
and1 : {0 x : _} -> Result0 x t ts e a -> Result0 (x && y) t ts e a
and1 (Succ0 val xs @{p}) = Succ0 val xs @{and1 p}
and1 (Fail0 err)         = Fail0 err

public export %inline
and2 : {0 x : _} -> Result0 x t ts e a -> Result0 (y && x) t ts e a
and2 r = swapAnd $ and1 r

public export %inline
trans :
     Result0 b1 t xs e a
  -> (0 _ : Suffix b2 xs ys)
  -> Result0 (b1 || b2) t ys e a
trans (Succ0 val ts @{p}) q = Succ0 val ts @{trans p q}
trans (Fail0 err)         _ = Fail0 err

public export %inline
succT :
      Result0 b1 t xs e a
  -> {auto 0 p : Suffix True xs ys}
  -> Result0 True t ys e a
succT r = swapOr $ trans r p

public export %inline
succF :
      Result0 b1 t xs e a
  -> {auto 0 p : Suffix True xs ys}
  -> Result0 False t ys e a
succF r = weaken $ trans r p

--------------------------------------------------------------------------------
--          Combinators
-----------------------------------------------------------------------------

public export
(<|>) :
     Result0 b1 t ts e a
  -> Lazy (Result0 b2 t ts e a)
  -> Result0 (b1 && b2) t ts e a
Succ0 v xs @{p} <|> _  = Succ0 v xs @{and1 p}
Fail0 _         <|> r2 = and2 r2

--------------------------------------------------------------------------------
--          Running a Parser
-----------------------------------------------------------------------------

||| Repeatedly consumes a strict prefix of a list of items
||| until the whole list is consumed.
|||
||| This is provably total, due to the strictness of the consuming
||| function.
public export
run :
     {0 t,e,a : Type}
  -> ((ts : List t) -> Result0 True t ts e a)
  -> List t -> Either e (List a)
run f cs = go [<] cs suffixAcc

  where
    go : SnocList a
      -> (ts : List t)
      -> (0 acc : SuffixAcc ts)
      -> Either e (List a)
    go sx [] _      = Right $ sx <>> []
    go sx xs (SA r) = case f xs of
      Succ0 v xs2 => go (sx :< v) xs2 r
      Fail0 err   => Left err

||| Repeatedly consumes a strict prefix of a list of characters
||| until the whole list is consumed. Drops all white space
||| it encounters (unsing `Prelude.isSpace` to determine, what is
||| a whitespace character).
|||
||| This is provably total, due to the strictness of the consuming
||| function.
public export
runDropWhitespace :
     {0 e,a : Type}
  -> ((cs : List Char) -> Result0 True Char cs e a)
  -> List Char -> Either e (List a)
runDropWhitespace f cs = go [<] cs suffixAcc

  where
    go : SnocList a
      -> (cs : List Char)
      -> (0 acc : SuffixAcc cs)
      -> Either e (List a)
    go sx [] _           = Right $ sx <>> []
    go sx (x::xs) (SA r) = 
      if isSpace x then go sx xs r
      else case f (x::xs) of
        Succ0 v xs2 => go (sx :< v) xs2 r
        Fail0 err   => Left err

--------------------------------------------------------------------------------
--          Erased Consumers
-----------------------------------------------------------------------------

public export
data TokError : Type -> Type where
  EOI         : TokError t
  ExpectedEOI : t -> TokError t
  Unexpected  : t -> TokError t

export
Interpolation t => Interpolation (TokError t) where
  interpolate (Unexpected t)  = "Unexpected item: \{t}"
  interpolate EOI             = "End of input"
  interpolate (ExpectedEOI t) = "Expected end of input but found: \{t}"

%runElab derive "TokError" [Show,Eq]

||| A tokenizing function, which will consume additional characters
||| from the input string. This can only be used if already some
||| have been consumed.
public export
0 AutoTok0 : (t,e,a : Type) -> Type
AutoTok0 t e a =
     {orig     : List t}
  -> (xs       : List t)
  -> {auto 0 p : Suffix True xs orig}
  -> Result0 True t orig e a

||| A tokenizing function that cannot fail.
public export
0 SafeTok0 : (t,a : Type) -> Type
SafeTok0 t a =
     {0 e      : Type}
  -> {orig     : List t}
  -> (xs       : List t)
  -> {auto 0 p : Suffix True xs orig}
  -> Result0 True t orig e a

||| A tokenizing function, which will consume additional items
||| from the input.
public export
0 OntoTok0 : (t,e,a : Type) -> Type
OntoTok0 t e a =
     {orig     : List t}
  -> (xs       : List t)
  -> {auto 0 p : Suffix False xs orig}
  -> Result0 True t orig e a

public export
head : OntoTok0 t (TokError t) t
head (x :: xs) = Succ0 x xs
head []        = Fail0 EOI

public export
eoi : AutoTok0 t (TokError t) ()
eoi []        = Succ0 () []
eoi (x :: _)  = Fail0 (ExpectedEOI x)

public export
takeOnto : SnocList t -> (n : Nat) -> AutoTok0 t (TokError t) (SnocList t)
takeOnto st 0     xs        = Succ0 st xs
takeOnto st (S k) (x :: xs) = takeOnto (st :< x) k xs
takeOnto st (S k) []        = Fail0 EOI

public export %inline
take : (n : Nat) -> AutoTok0 t (TokError t) (SnocList t)
take = takeOnto [<]

public export %inline
take1 : (n : Nat) -> (0 _ : IsSucc n) => OntoTok0 t (TokError t) (SnocList t)
take1 (S n) (x :: xs) = takeOnto [<x] n xs
take1 _     []        = Fail0 EOI

public export
takeWhileOnto : SnocList t -> (t -> Bool) -> SafeTok0 t (SnocList t)
takeWhileOnto st f (x :: xs) =
  if f x then takeWhileOnto (st :< x) f xs else Succ0 st (x::xs)
takeWhileOnto st f []        = Succ0 st []

public export %inline
takeWhile : (t -> Bool) -> SafeTok0 t (SnocList t)
takeWhile = takeWhileOnto [<]

public export %inline
takeWhile1 : (t -> Bool) -> OntoTok0 t (TokError t) (SnocList t)
takeWhile1 f (x :: xs) =
  if f x then takeWhileOnto [<x] f xs else Fail0 (Unexpected x)
takeWhile1 f [] = Fail0 EOI

public export %inline
takeUntil : (t -> Bool) -> SafeTok0 t (SnocList t)
takeUntil f = takeWhile (not . f)

public export %inline
takeUntil1 : (t -> Bool) -> OntoTok0 t (TokError t) (SnocList t)
takeUntil1 f = takeWhile1 (not . f)

public export
takeWhileJustOnto : SnocList s -> (t -> Maybe s) -> SafeTok0 t (SnocList s)
takeWhileJustOnto st f (x :: xs) = case f x of
  Just vs => takeWhileJustOnto (st :< vs) f xs
  Nothing => Succ0 st (x::xs)
takeWhileJustOnto st f []        = Succ0 st []

public export %inline
takeWhileJust : (t -> Maybe s) -> SafeTok0 t (SnocList s)
takeWhileJust = takeWhileJustOnto [<]

public export
takeWhileJust1 : (t -> Maybe s) -> OntoTok0 t (TokError t) (SnocList s)
takeWhileJust1 f (x :: xs) = case f x of
  Just vs => takeWhileJustOnto [<vs] f xs
  Nothing => Fail0 (Unexpected x)
takeWhileJust1 f []        = Fail0 EOI

public export %inline
accum : s -> (s -> t -> Maybe s) -> SafeTok0 t s
accum cur f (x::xs) = case f cur x of
  Just s2 => accum s2 f xs
  Nothing => Succ0 cur (x::xs)
accum cur f [] = Succ0 cur []

public export %inline
accum1 : s -> (s -> t -> Maybe s) -> OntoTok0 t (TokError t) s
accum1 cur f (x::xs) = case f cur x of
  Just s2 => accum s2 f xs
  Nothing => Fail0 (Unexpected x)
accum1 cur f [] = Fail0 EOI

public export
data AccumRes : (state,err : Type) -> Type where
  Done  : {0 state,err : _} -> AccumRes state err
  Cont  : {0 state,err : _} -> state -> AccumRes state err
  Error : {0 state,err : _} -> err -> AccumRes state err

public export %inline
accumErr : s -> (s -> x) -> (s -> t -> AccumRes s e) -> AutoTok0 t e x
accumErr cur f g (x::xs) = case g cur x of
  Done      => Succ0 (f cur) (x::xs)
  Cont s'   => accumErr s' f g xs
  Error err => Fail0 err
accumErr cur f g [] = Succ0 (f cur) []
