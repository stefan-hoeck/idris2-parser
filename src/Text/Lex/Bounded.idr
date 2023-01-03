module Text.Lex.Bounded

import Derive.Prelude

%default total

%language ElabReflection

public export
record Bounds where
  constructor MkBounds
  ||| 0-based first line
  startLine : Nat
  ||| 0-based first col
  startCol : Nat
  ||| 0-based last line of bound
  endLine : Nat
  ||| 0-based first column after bound
  endCol : Nat

%runElab derive "Bounds" [Show,Eq]

namespace Bounds
  public export
  start : Bounds -> (Nat, Nat)
  start b = (b.startLine, b.startCol)

  public export
  end : Bounds -> (Nat, Nat)
  end b = (b.endLine, b.endCol)

public export
Semigroup Bounds where
  x <+> y =
    let (ur, uc) := min (start x) (start y)
        (lr, lc) := max (end x) (end y)
     in MkBounds ur uc lr lc

public export
record WithBounds ty where
  constructor MkBounded
  val    : ty
  bounds : Maybe Bounds

%runElab derive "WithBounds" [Show,Eq]

public export
Functor WithBounds where
  map f (MkBounded val bs) = MkBounded (f val) bs

public export
Foldable WithBounds where
  foldr c n b = c b.val n
  foldl c n b = c n b.val
  foldMap f b = f b.val
  null _ = False
  toList b = [b.val]

public export
Traversable WithBounds where
  traverse f (MkBounded v bs) = (`MkBounded` bs) <$> f v

namespace WithBounds
  public export %inline
  start : WithBounds ty -> Maybe (Nat, Nat)
  start = map start . bounds

  public export %inline
  end : WithBounds ty -> Maybe (Nat, Nat)
  end = map end . bounds

public export %inline
irrelevantBounds : ty -> WithBounds ty
irrelevantBounds x = MkBounded x Nothing

public export
mergeBounds : WithBounds ty -> WithBounds ty' -> WithBounds ty'
mergeBounds (MkBounded _ $ Just x) (MkBounded val $ Just y) = MkBounded val (Just $ x <+> y)
mergeBounds (MkBounded _ x)        (MkBounded val y)        = MkBounded val (x <|> y)

public export
joinBounds : WithBounds (WithBounds ty) -> WithBounds ty
joinBounds b = mergeBounds b b.val
