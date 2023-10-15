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
     (t : Type)
  -> List t
  -> (e,a : Type)
  -> Type where

  Succ :
       {0 t,e,a : Type}
    -> {0 ts : List t}
    -> (val : a)
    -> (xs : List t)
    -> {auto p : Suffix False xs ts}
    -> Result t ts e a

  Fail :
       {0 t,e,a : Type}
    -> {ts,stopStart : List t}
    -> (start : Suffix False stopStart ts)
    -> (0 errEnd : List t)
    -> {auto end : Suffix False errEnd stopStart}
    -> (reason : e)
    -> Result t ts e a

||| Alias for `Succ`, which takes the proof as an
||| explicit argument
public export %inline
succ : 
       {0 t,e,a : Type}
    -> {0 ts : List t}
    -> (val : a)
    -> {xs : List t}
    -> Suffix False xs ts
    -> Result t ts e a
succ val _ = Succ val xs

public export
Functor (Result t ts e) where
  map f (Succ v xs)    = Succ (f v) xs
  map _ (Fail st ee r) = Fail st ee r

--------------------------------------------------------------------------------
--          Conversions
--------------------------------------------------------------------------------

public export %inline
trans : {ys : _} -> Result t xs e a -> Suffix False xs ys -> Result t ys e a
trans (Succ val ts @{p}) q = Succ val ts @{trans p q}
trans (Fail {stopStart} x y err) q = Fail {stopStart} (trans x q) y err

public export %inline
succT : {ys : _} ->  Result t xs e a -> Suffix False xs ys => Result t ys e a
succT r @{p} = trans r p
