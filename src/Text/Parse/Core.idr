module Text.Parse.Core

import Data.Bool
import Data.List
import Data.List1
import Data.List.Suffix
import Derive.Prelude
import Text.Parse.Err
import Text.Parse.FC
import Text.Lex.Bounded
import Text.Lex.Core
import Text.Lex.Tokenizer

%language ElabReflection
%default total

--------------------------------------------------------------------------------
--          Parsing Results
--------------------------------------------------------------------------------

||| Result of running a parser.
public export
data Res :
     (strict : Bool)
  -> (ts : List $ WithBounds t)
  -> (state,e,a : Type)
  -> Type where

  Fail  :
       {0 b : Bool}
    -> {0 state,t,e,a : Type}
    -> {0 ts : List $ WithBounds t}
    -> (err  : List1 $ WithBounds $ ParseErr e)
    -> Res b ts state e a

  Pure :
       {0 state,t,e,a : Type}
    -> state
    -> (res   : WithBounds a)
    -> (toks  : List $ WithBounds t)
    -> Res False toks state e a

  Succ :
       {0 b : Bool}
    -> {0 state,t,e,a : Type}
    -> {0 ts : List $ WithBounds t}
    -> state
    -> (res   : WithBounds a)
    -> (toks  : List $ WithBounds t)
    -> (0 prf : Suffix True toks ts)
    -> Res b ts state e a

namespace Res
  public export %inline
  fail_ : WithBounds (ParseErr e) -> Res b ts s e a
  fail_ = Fail . singleton

  public export %inline
  parseFail : ParseErr e -> Res b ts s e a
  parseFail = fail_ . irrelevantBounds

  public export %inline
  fail : e -> Res b ts s e a
  fail = parseFail . Custom

  public export %inline
  parseFailLoc : Maybe Bounds -> ParseErr e -> Res b ts s e a
  parseFailLoc b err = fail_ (MkBounded err b)

  public export %inline
  failLoc : Maybe Bounds -> e -> Res b ts s e a
  failLoc b = parseFailLoc b . Custom

public export
merge : WithBounds z -> Res b ts s e a -> Res b ts s e a
merge x (Succ y res toks prf) = Succ y (mergeBounds x res) toks prf
merge x (Pure y res toks)     = Pure y (mergeBounds x res) toks
merge x v                     = v

export
succ : Res b ts s e a -> (0 p : Suffix True ts ts') -> Res b1 ts' s e a
succ (Fail err) p = Fail err
succ (Pure x res ts) p = Succ x res ts p
succ (Succ x res toks prf) p = Succ x res toks (prf ~> p)

--------------------------------------------------------------------------------
--          Grammar
--------------------------------------------------------------------------------

public export %tcinline
0 inf : Bool -> Type -> Type
inf False y = y
inf True  y = Inf y

public export
data Grammar :
     (strict : Bool)
  -> (state,t,e,a : Type)
  -> Type where

  Lift :
       {0 state,t,e,a : Type}
    -> (state -> (ts : List $ WithBounds t) -> Res b ts state e a)
    -> Grammar b state t e a

  SeqEat :
       {0 state,t,e,a : Type}
    -> Grammar True state t e a
    -> Inf (a -> Grammar b2 state t e b)
    -> Grammar True state t e b
  
  ThenEat :
       {0 state,t,e,a : Type}
    -> Grammar True state t e a
    -> Inf (Grammar b2 state t e b)
    -> Grammar True state t e b

  Bind :
      {0 state,t,e,a : Type}
   -> Grammar b1 state t e a
   -> (a -> Grammar b2 state t e b)
   -> Grammar (b1 || b2) state t e b

  Catch :
      {0 state,t,e,a : Type}
   -> Grammar b1 state t e a
   -> (List1 (WithBounds $ ParseErr e) -> Grammar b2 state t e a)
   -> Grammar (b1 && b2) state t e a

  Bounds :
      {0 state,t,e,a : Type}
   -> Grammar b state t e a
   -> Grammar b state t e (WithBounds a)

--------------------------------------------------------------------------------
--          Error Handling
--------------------------------------------------------------------------------

public export %inline
fail_ :
     {0 state,t,e,a : Type}
  -> WithBounds (ParseErr e)
  -> Grammar b state t e a 
fail_ err = Lift $ \_,_ => fail_ err

||| Always fail with the given error
public export %inline
fail : {0 state,t,e,a : Type} -> e -> Grammar b state t e a
fail err = fail_ (irrelevantBounds $ Custom err)

||| Always fail with a message and a location
public export %inline
failLoc : {0 state,t,e,a : Type} -> Maybe Bounds -> e -> Grammar b state t e a
failLoc bs err = fail_ (MkBounded (Custom err) bs)

-------------------------------------------------------------------------------
--         Core Parsers
-------------------------------------------------------------------------------

public export %tcinline
(>>=) :
     {0 state,t,e,a : Type}
  -> {b1 : _}
  -> Grammar b1 state t e a
  -> inf b1 (a -> Grammar b2 state t e b)
  -> Grammar (b1 || b2) state t e b
(>>=) {b1 = False} x f = Bind x f
(>>=) {b1 = True}  x f = SeqEat x f

public export %inline
(>>) :
     {0 state,t,e,a : Type}
  -> {b1 : _}
  -> Grammar b1 state t e ()
  -> inf b1 (Grammar b2 state t e b)
  -> Grammar (b1 || b2) state t e b
(>>) {b1 = False} x y = Bind x (const y)
(>>) {b1 = True}  x y = ThenEat x y

public export
(<|>) :
     {0 b1,b2 : Bool}
  -> {0 state,t,e,a : Type}
  -> Grammar b1 state t e a
  -> Lazy (Grammar b2 state t e a)
  -> Grammar (b1 && b2) state t e a
x <|> y = Catch x (\_ => y)

public export %inline
pure : {0 state,t,e,a : Type} -> (res : a) -> Grammar False state t e a
pure res = Lift $ \s,ts => Pure s (irrelevantBounds res) ts

public export
Functor (Grammar b s t e) where
  map f g = rewrite sym (orFalseNeutral b) in Bind g (pure . f)

public export %inline
(<*>) :
     {0 b1,b2 : Bool}
  -> {0 state,t,e,a : Type}
  -> Grammar b1 state t e (a -> b)
  -> Grammar b2 state t e a
  -> Grammar (b1 || b2) state t e b
(<*>) x y = Bind x (\f => map f y)

public export
some : Grammar True s t e a -> Grammar True s t e (List a)

public export
many : Grammar True s t e a -> Grammar False s t e (List a)

some g = Core.do
  v  <- g
  vs <- many g
  pure (v :: vs)

many g = some g <|> pure []

||| Check whether the next token satisfies a predicate
public export
nextIs : Lazy e -> (t -> Bool) -> Grammar False s t e t
nextIs err f = Lift $ \s,cs => case cs of
  h :: t =>
    if f h.val then Pure s h _ else failLoc h.bounds err
  []     => parseFail EOI

||| Look at the next token in the input
public export
peek : Grammar False s t e t
peek = Lift $ \s,cs => case cs of
  h :: t => Pure s h _
  []     => parseFail EOI

||| Look at the next token in the input
public export
terminal : (t -> Either e a) -> Grammar True s t e a
terminal f = Lift $ \s,cs => case cs of
  h :: t => case f h.val of
    Right v => Succ s (MkBounded v h.bounds) t %search
    Left e  => failLoc h.bounds e
  []     => parseFail EOI

prs :
     {0 state,t,e,a : Type}
  -> Grammar b state t e a
  -> state
  -> (ts : List $ WithBounds t)
  -> (0 acc : SuffixAcc ts)
  -> Res b ts state e a
prs (Lift f) y ts _ = f y ts
prs (SeqEat x y) s ts (Access rec) = case prs x s ts (Access rec) of
  Succ s2 res ts2 p => merge res $ succ (prs (y res.val) s2 ts2 (rec ts2 p)) p
  Fail err => Fail err
prs (ThenEat x y) s ts (Access rec) = case prs x s ts (Access rec) of
  Succ s2 res ts2 p => merge res $ succ (prs y s2 ts2 (rec ts2 p)) p
  Fail err => Fail err
prs (Bind x y) s ts (Access rec) = case prs x s ts (Access rec) of
  Succ s2 res ts2 p => merge res $ succ (prs (y res.val) s2 ts2 (rec ts2 p)) p
  Pure s2 res ts2   => merge res $ prs (y res.val) s2 ts2 (Access rec)
  Fail err          => Fail err
prs (Catch x f) s ts acc = case prs x s ts acc of
  Succ s2 res ts2 p => Succ s2 res ts2 p
  Pure s2 res ts2   => Pure s2 res ts2
  Fail {b = b1} err => case prs (f err) s ts acc of
    Succ s2 res ts2 p => Succ s2 res ts2 p
    Pure s2 res ts2   => rewrite andFalseFalse b1 in Pure s2 res ts2
    Fail err2         => Fail $ err ++ err2
prs (Bounds x) s ts acc = case prs x s ts acc of
  Succ s2 res ts2 p => Succ s2 (MkBounded res res.bounds) ts2 p
  Pure s2 res ts2   => Pure s2 (MkBounded res res.bounds) ts2
  Fail err          => Fail err

export
parse :
     {0 state,t,e,a : Type}
  -> Grammar b state t e a
  -> state
  -> (ts : List $ WithBounds t)
  -> Either (List1 $ WithBounds $ ParseErr e) (state, a, List $ WithBounds t)
parse g s ts = case prs g s ts (ssAcc _) of
  Fail errs           => Left errs
  Pure x res ts       => Right (x, res.val, ts)
  Succ x res toks prf => Right (x, res.val, ts)

--------------------------------------------------------------------------------
--          Combining Lexers and Parsers
--------------------------------------------------------------------------------

filterOnto :
     List (WithBounds t)
  -> (t -> Bool)
  -> SnocList (WithBounds t)
  -> List (WithBounds t)
filterOnto xs f (sx :< x) =
  if f x.val then filterOnto (x :: xs) f sx else filterOnto xs f sx
filterOnto xs f [<]       = xs

export
lexAndParse :
     {0 state,t,e,a : Type}
  -> Origin
  -> Tokenizer t
  -> (keep : t -> Bool)
  -> Grammar b state t e a
  -> state
  -> String
  -> Either (ReadError e) (state, a)
lexAndParse orig tm keep gr s str = case lex tm str of
  TR l c st EndInput _ _ => case parse gr s (filterOnto [] keep st) of
    Left x          => ?foo_0
    Right (s2,a,[]) => Right (s2,a)
    Right (s2,a,ts) => Right (s2,a)
  TR l c st r _ _ => Left (LexFailed (FC orig $ Just $ MkBounds l c l (c+1)) r)
