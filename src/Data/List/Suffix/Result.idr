module Data.List.Suffix.Result

import Data.Bool.Rewrite
import public Data.List.Suffix

%default total

||| Result of consuming and converting a (possibly strict) prefix
||| of a list of tokens.
|||
||| This comes with a non-erased proof about the number of tokens
||| consumed, which can be used to for instance 
||| calculate the bounds of a lexeme. Likewise, the error specifies
||| a start and end suffix for calculating proper bounds in case
||| of an error.
|||
||| Use this for writing simple, high-performance tokenizers, which
||| (in the case of strict results) are guaranteed to terminate.
||| See module `Text.Lex.Manual` for
||| utilities for consuming and converting prefixes
||| of tokens, but for a nicer interface, consider using `Text.Lex.Tokenizer`
||| (at the cost of a drop in performance).
|||
||| @ strict : True if a strict prefix of the list of tokens has
|||            been consumed.
||| @ t      : the type of token consumed.
||| @ ts     : the original list of tokens
||| @ e      : the error type in case of a failure
||| @ a      : the result type
public export
data Result :
     (strict : Bool)
  -> (t : Type)
  -> List t
  -> (e,a : Type)
  -> Type where

  Succ :
       {0 b : Bool}
    -> {0 t,e,a : Type}
    -> {0 ts : List t}
    -> (val : a)
    -> (xs : List t)
    -> {auto p : Suffix b xs ts}
    -> Result b t ts e a

  Fail :
       {0 b : Bool}
    -> {0 t,e,a : Type}
    -> {ts,stopStart : List t}
    -> (start : Suffix False stopStart ts)
    -> (0 errEnd : List t)
    -> {auto end : Suffix False errEnd stopStart}
    -> (reason : e)
    -> Result b t ts e a

||| Alias for `Succ`, which takes the proof as an
||| explicit argument
public export %inline
succ : 
       {0 b : Bool}
    -> {0 t,e,a : Type}
    -> {0 ts : List t}
    -> (val : a)
    -> {xs : List t}
    -> Suffix b xs ts
    -> Result b t ts e a
succ val _ = Succ val xs

public export
Functor (Result b t ts e) where
  map f (Succ v xs)    = Succ (f v) xs
  map _ (Fail st ee r) = Fail st ee r

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
swapOr : {0 x,y : _} -> Result (x || y) t ts e a -> Result (y || x) t ts e a
swapOr = swapOr (\k => Result k t ts e a)

public export %inline
orSame : {0 x : _} -> Result (x || x) t ts e a -> Result x t ts e a
orSame = orSame (\k => Result k t ts e a)

public export %inline
orTrue : {0 x : _} -> Result (x || True) t ts e a -> Result True t ts e a
orTrue = orTrue (\k => Result k t ts e a)

public export %inline
orFalse : {0 x : _} -> Result (x || False) t ts e a -> Result x t ts e a
orFalse = orFalse (\k => Result k t ts e a)

public export %inline
swapAnd : {0 x,y : _} -> Result (x && y) t ts e a -> Result (y && x) t ts e a
swapAnd = swapAnd (\k => Result k t ts e a)

public export %inline
andSame : {0 x : _} -> Result (x && x) t ts e a -> Result x t ts e a
andSame = andSame (\k => Result k t ts e a)

public export %inline
andTrue : {0 x : _} -> Result (x && True) t ts e a -> Result x t ts e a
andTrue = andTrue (\k => Result k t ts e a)

public export %inline
andFalse : {0 x : _} -> Result (x && False) t ts e a -> Result False t ts e a
andFalse = andFalse (\k => Result k t ts e a)

public export %inline
weaken : {0 x : _} -> Result x t ts e a -> Result False t ts e a
weaken (Succ val xs @{p}) = Succ val xs @{weaken p}
weaken (Fail x y err) = Fail x y err

public export %inline
weakens : {0 x : _} -> Result True t ts e a -> Result x t ts e a
weakens (Succ val xs @{p}) = Succ val xs @{weakens p}
weakens (Fail x y err) = Fail x y err

public export %inline
and1 : {0 x : _} -> Result x t ts e a -> Result (x && y) t ts e a
and1 (Succ val xs @{p}) = Succ val xs @{and1 p}
and1 (Fail x y err) = Fail x y err

public export %inline
and2 : {0 x : _} -> Result x t ts e a -> Result (y && x) t ts e a
and2 r = swapAnd $ and1 r

public export %inline
trans :
     {ys : _}
  -> Result b1 t xs e a
  -> Suffix b2 xs ys
  -> Result (b1 || b2) t ys e a
trans (Succ val ts @{p}) q = Succ val ts @{p ~> q}
trans (Fail {stopStart} x y err) q = Fail {stopStart} (x ~?> q) y err

||| Operator alias for `trans`.
public export %inline
(~>) :
     {ys : _}
  -> Result b1 t xs e a
  -> Suffix b2 xs ys
  -> Result (b1 || b2) t ys e a
(~>) = trans

||| Flipped version of `(~>)`.
public export %inline
(<~) :
     {ys : _}
  -> Suffix b1 xs ys
  -> Result b2 t xs e a
  -> Result (b1 || b2) t ys e a
x <~ y = swapOr $ trans y x

||| Operator alias for `trans` where the result is always non-strict
public export %inline
(~?>) :
     {ys : _}
   -> Result b1 t xs e a
   -> Suffix b2 xs ys
   -> Result False t ys e a
(~?>) x y = weaken $ x ~> y

||| Operator alias for `trans` where the strictness of the first
||| `Suffix` dominates.
public export %inline
(~~>) :
     {ys : _}
  -> Result b1 t xs e a
  -> Suffix True xs ys
  -> Result b1 t ys e a
(~~>) x y = weakens $ y <~ x

||| Operator alias for `trans` where the strictness of the second
||| `Suffix` dominates.
public export %inline
(<~~) :
     {ys : _}
  -> Suffix b1 xs ys
  -> Result True t xs e a
  -> Result b1 t ys e a
(<~~) x y = weakens $ y ~> x

public export %inline
succT :
      {ys : _}
  ->  Result b1 t xs e a
  -> {auto p : Suffix True xs ys}
  -> Result True t ys e a
succT r = p <~ r

public export %inline
succF :
      {ys : _}
  ->  Result b1 t xs e a
  -> {auto p : Suffix True xs ys}
  -> Result False t ys e a
succF r = r ~?> p
