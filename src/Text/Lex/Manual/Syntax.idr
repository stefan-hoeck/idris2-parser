module Text.Lex.Manual.Syntax

import Text.Lex.Manual

%default total

public export
pure : a -> Tok False e a
pure v cs = Succ v cs

public export
(<*>) : Tok b1 e (a -> b) -> Tok b2 e a -> Tok (b1 || b2) e b
(<*>) t1 t2 cs =
  let Succ fun cs1 @{p1} := t1 cs | Fail x y z => Fail x y z
   in swapOr $ fun <$> trans (t2 cs1) p1
