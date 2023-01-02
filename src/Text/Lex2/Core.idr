||| A simple library of lexers and their combinators. A `Lexer` is
||| just a (dependent) function, which is guaranteed to consume a non-empty
||| prefix of the input list of characters.
|||
||| As such, high-performance lexers can be written manually, while
||| many convenient combinators exist for less performance-critical
||| applications.
module Text.Lex2.Core

import public Data.List
import public Data.List.Suffix
import public Data.SnocList
import public Text.Lex.Bounded

%default total

||| Result of running a lexer once: The lexer either stops, when
||| can no longer consume any characters, or it consumed some
||| characters and returns (a possibly `strict`) suffix of the
||| input character sequence.
public export
data Rec : (strict  : Bool) -> (cs : List Char) -> Type where
  Stop : Rec s cs
  Res :  (sc    : SnocList Char)
      -> (toks  : List Char)
      -> (0 prf : Suffix_ s toks cs)
      -> Rec s cs

||| this is the identity at runtim
export
mapPrf :
     (0 f : forall as . Suffix_ s1 as bs -> Suffix_ s2 as cs)
  -> Rec s1 bs
  -> Rec s2 cs
mapPrf f Stop              = Stop
mapPrf f (Res sc toks prf) = Res sc toks (f prf)

export %inline
(~>) : Rec s1 bs -> (0 p : Suffix_ s2 bs cs) -> Rec (s2 || s1) cs
r ~> p = mapPrf (\q => swapOr $ q ~> p) r

export %inline
(~?>) : Rec s1 bs -> (0 p : Suffix_ s2 bs cs) -> Rec False cs
r ~?> p = mapPrf (~?> p) r

export %inline
(~~>) : Rec s1 bs -> (0 p : Suffix_ s2 bs cs) -> Rec s2 cs
r ~~> p = mapPrf (~~> p) r

namespace Rec
  export
  (<|>) : Rec b1 cs -> Lazy (Rec b2 cs) -> Rec (b1 && b2) cs
  (<|>) r@(Res _ _ _) _  = mapPrf and1 r
  (<|>) Stop          r  = mapPrf and2 r

||| A function, recognising a (possibly) empty sequence of characters.
||| If the boolean argument is set to `True`, this is a `Lexer`, which
||| is guaranteed to consume some input.
public export
0 Recognise : Bool -> Type
Recognise b = SnocList Char -> (cs : List Char) -> Rec b cs

||| Alias for `Recognise True`.
public export
0 Lexer : Type
Lexer = Recognise True

||| The empty lexer, which never consumes any input.
export %inline
empty : Recognise False
empty sc cs = Res sc cs Same

||| Choice between two lexers. Consumes input, if both lexers consume input.
export %inline
(<|>) : Recognise b1 -> Recognise b2 -> Recognise (b1 && b2)
(<|>) r1 r2 sc cs = r1 sc cs <|> r2 sc cs

||| Renders the given lexer optional.
export %inline
opt : Lexer -> Recognise False
opt l = l <|> empty

||| Recognises the end of input.
export %inline
eof : Recognise False
eof sc [] = Res sc [] Same
eof _ _  = Stop

||| Positive look-ahead. Does not consume any input.
export
expect : Recognise b -> Recognise False
expect f sc cs = case f sc cs of
  Res {} => Res sc cs Same
  Stop   => Stop

||| Negative look-ahead. Does not consume any input.
export
reject : Recognise b -> Recognise False
reject f sc cs = case f sc cs of
  Res {} => Stop
  Stop   => Res sc cs Same

||| The lexer which always fails.
export %inline
stop : Lexer
stop _ _ = Stop

||| Sequencing of two lexers. Consumes, if any of the two consume.
export
(<+>) : Recognise b1 -> Recognise b2 -> Recognise (b1 || b2)
(<+>) r1 r2 sc cs = case r1 sc cs of
  Res sc1 cs1 p1 => r2 sc1 cs1 ~> p1
  Stop           => Stop

manyOnto :
     Lexer
  -> SnocList Char
  -> (cs    : List Char)
  -> (0 acc : SuffixAcc cs)
  -> Rec False cs
manyOnto f sc cs (Access rec) = case f sc cs of
  Res sc2 cs2 p2 => manyOnto f sc2 cs2 (rec cs2 p2) ~?> p2
  Stop           => Res sc cs Same

||| Runs the given lexer zero or more times.
export
many : Lexer -> Recognise False
many f sc cs = manyOnto f sc cs (ssAcc _)

||| Runs the given lexer several times, but at least once.
export
some : Lexer -> Lexer
some f sc cs = case f sc cs of
  Res sc2 cs2 p => manyOnto f sc2 cs2 (ssAcc _) ~~> p
  Stop          => Stop

||| Lexer consiming one character if it fulfills the given predicate.
export
pred : (Char -> Bool) -> Lexer
pred f sc (x :: xs) = case f x of
  True  => Res (sc :< x) xs cons1
  False => Stop
pred f sc []        = Stop
-- 
-- predsOnto : SnocList Char -> (Char -> Bool) -> Recognise False
-- predsOnto sc f (x :: xs) = case f x of
--   True  => predsOnto (sc :< x) f xs ~?> cons1
--   False => Res sc (x :: xs) Same
-- predsOnto sc f []        = Res sc [] Same

||| Recogniser consuming characters while they fulfill the given predicate.
||| This is an optimized version of `many . pred`.
export %inline
preds0 : (Char -> Bool) -> Recognise False
preds0 f sc (x :: xs) = case f x of
  True  => preds0 f (sc :< x) xs ~?> cons1
  False => Res sc (x :: xs) Same
preds0 f sc [] = Res sc [] Same

||| Lexer consuming characters while they fulfill the given predicate.
||| This is an optimized version of `some . pred`.
export
preds : (Char -> Bool) -> Lexer
preds f sc (x :: xs) = case f x of
  True  => preds0 f (sc :< x) xs ~~> cons1
  False => Stop
preds f sc [] = Stop

cmap : (a -> Recognise c) -> (xs : List a) -> Recognise False
cmap f (x :: xs) sc cs = case f x sc cs of
   Res sc2 cs2 p2 => cmap f xs sc2 cs2 ~?> p2
   Stop           => Stop
cmap f [] sc  cs = Res sc cs Same

export
concatMap : (a -> Recognise c) -> (xs : List a) -> Recognise (isCons xs && c)
concatMap f (x :: xs) sc cs = case f x sc cs of
  Res sc2 cs2 p => cmap f xs sc2 cs2 ~~> p
  Stop         => Stop
concatMap f [] sc cs = Res sc cs Same

--------------------------------------------------------------------------------
--          Lex
--------------------------------------------------------------------------------

lineCol : (line,col,cur : Nat) -> SnocList Char -> (Nat,Nat)
lineCol l c cur [<]          = (l, c + cur)
lineCol l c cur (sx :< '\n') = (S l + count ('\n' ==) sx, cur)
lineCol l c cur (sx :< x)    = lineCol l c (S cur) sx

public export
0 TokenMap : (tokenType : Type) -> Type
TokenMap tokenType = List (Lexer, SnocList Char -> tokenType)

record Step (a : Type) (cs : List Char) where
  constructor ST
  line  : Nat
  col   : Nat
  res   : WithBounds a
  rem   : List Char
  0 prf : StrictSuffix rem cs

step : (l, c : Nat) -> TokenMap a -> (cs : List Char) -> Maybe (Step a cs)
step l c ((f,g) :: ps) cs = case f [<] cs of
  Res sc cs2 p =>
    let (l2,c2) := lineCol l c 0 sc
        bnds    := Just $ MkBounds l c l2 c2
     in Just $ ST l2 c2 (MkBounded (g sc) bnds) cs2 p
  Stop         => step l c ps cs
step _ _ [] _ = Nothing

tokenise :
     (a -> Bool)
  -> (line, col : Nat)
  -> SnocList (WithBounds a)
  -> TokenMap a
  -> (cs    : List Char)
  -> (0 acc : SuffixAcc cs)
  -> (SnocList (WithBounds a), (Nat, Nat, List Char))
tokenise f l c sx xs cs (Access rec) = case step l c xs cs of
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
