module Text.Parse.Syntax

import Text.Parse.Manual

%default total

%hide Prelude.(*>)
%hide Prelude.(<*)
%hide Prelude.(<*>)
%hide Prelude.pure

--------------------------------------------------------------------------------
--          Applicative Syntax
--------------------------------------------------------------------------------

public export %inline
pure : a -> Grammar False t e a
pure v xs = Succ0 v xs

public export %inline
(<*>) : Grammar b1 t e (a -> b) -> Grammar b2 t e a -> Grammar (b1 || b2) t e b
(<*>) gf ga xs =
  let Succ0 f r1 @{p} := gf xs | Fail0 err => Fail0 err
      Succ0 v r2 @{q} := ga r1 | Fail0 err => Fail0 err
   in Succ0 (f v) r2 @{swapOr $ trans q p}

public export %inline
(*>) : Grammar b1 t e () -> Grammar b2 t e a -> Grammar (b1 || b2) t e a
(*>) g1 g2 xs =
  let Succ0 () r1 @{p} := g1 xs | Fail0 err => Fail0 err
      Succ0 v  r2 @{q} := g2 r1 | Fail0 err => Fail0 err
   in Succ0 v r2 @{swapOr $ trans q p}

||| Version of `(*>)` specialized for strict second grammars
public export %inline
seqt : Grammar b t e () -> Grammar True t e a -> Grammar True t e a
seqt x y = orTrue $ x *> y

public export %inline
(<*) : Grammar b1 t e a -> Grammar b2 t e () -> Grammar (b1 || b2) t e a
(<*) g1 g2 xs =
  let Succ0 v  r1 @{p} := g1 xs | Fail0 err => Fail0 err
      Succ0 () r2 @{q} := g2 r1 | Fail0 err => Fail0 err
   in Succ0 v r2 @{swapOr $ trans q p}

--------------------------------------------------------------------------------
--          Parentheses
--------------------------------------------------------------------------------

||| Drops the given token after parsing the given grammar
public export %inline
before : Eq t => Grammar b t e a -> (c : t) -> Grammar True t e a
before f c = orTrue $ f <* exact c

||| Drops the given token before parsing the given grammar
public export %inline
after : Eq t => (o : t) -> Grammar b t e a -> Grammar True t e a
after o f = exact o *> f

||| Wrapps the given grammar between an opening and closing token.
|||
||| Note: This fails with an `Unclosed` exception if the end of
|||       input is reached without closing the opening token.
public export %inline
between : Eq t => (o,c : t) -> Grammar b t e a -> Grammar True t e a
between o c f (B x b :: xs) = case o == x of
  False => expected b o
  True  =>
    let Succ0 v (B y b2 :: ys) := succT (f xs) | res => failInParen b x res
     in if c == y then Succ0 v ys else unexpected (B y b2)
between o c f [] = eoi

--------------------------------------------------------------------------------
--          Lists
--------------------------------------------------------------------------------

public export
optional : Grammar b t e a -> Grammar False t e (Maybe a)
optional f ts = weaken $ (Just <$> f ts) <|> Succ0 Nothing ts @{Same}

public export
manyOnto :
     (fatal : ParseError t e -> Bool)
  -> Grammar True t e a
  -> SnocList a
  -> AccGrammar False t e (List a)
manyOnto fatal f sx ts (SA r) = case f ts of
  Succ0 v ys => succF $ manyOnto fatal f (sx :< v) ys r 
  Fail0 x    => if fatal x.val then Fail0 x else Succ0 (sx <>> []) ts

||| Runs the given parser zero or more times, accumulating the
||| results in a list.
|||
||| Note: This will fail in case of a fatal error, which allows for
|||       more fine-grained control over whether a parser is successful
|||       or not.
public export %inline
manyF :
     (fatal : ParseError t e -> Bool)
  -> Grammar True t e a
  -> Grammar False t e (List a)
manyF fatal f ts = manyOnto fatal f [<] ts suffixAcc

||| Runs the given parser zero or more times, accumulating the
||| results in a list.
|||
||| Note: This will never fail, even if the given parser fails
|||       with an error that should be fatal. User `manyF` to
|||       have the ability to specify fatal errors.
public export %inline
many : Grammar True t e a -> Grammar False t e (List a)
many = manyF (const False)

||| Runs the given parser one or more times, accumulating the
||| results in a non-empty list.
|||
||| Note: This will fail in case of a fatal error, even when parsing
|||       the tail of the list, which allows for
|||       more fine-grained control over whether a parser is successful
|||       or not.
public export %inline
someF :
     (fatal : ParseError t e -> Bool)
  -> Grammar True t e a
  -> Grammar True t e (List1 a)
someF fatal f = [| f ::: manyF fatal f|]

||| Runs the given parser one or more times, accumulating the
||| results in a non-empty list.
|||
||| Note: User `manyF` for the ability to specify fatal errors.
public export %inline
some : Grammar True t e a -> Grammar True t e (List1 a)
some = someF (const False)

||| Runs the given parser one or more times, separating occurences with
||| the given separator.
|||
||| Note: This will fail in case of a fatal error, even when parsing
|||       the tail of the list, which allows for
|||       more fine-grained control over whether a parser is successful
|||       or not.
|||
|||       Consider using `sepByExact1` for better error behavior,
|||       if the separator consists of a single, constant token.
public export %inline
sepByF1 :
     (fatal : ParseError t e -> Bool)
  -> (sep : Grammar b t e ())
  -> Grammar True t e a
  -> Grammar True t e (List1 a)
sepByF1 fatal sep f = [| f ::: manyF fatal (seqt sep f)|]

||| Like `sepBy1` but with better error behavior:
||| If the separator was recognized, this fails instead of
||| aborting with a partial list.
public export %inline
sepByExact1 :
     Eq t
  => Eq e
  => (sep : t)
  -> Grammar True t e a
  -> Grammar True t e (List1 a)
sepByExact1 sep = sepByF1 (/= Expected sep) (exact sep)
