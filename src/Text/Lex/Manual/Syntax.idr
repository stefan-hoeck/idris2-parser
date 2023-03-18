module Text.Lex.Manual.Syntax

import Text.Lex.Manual

%default total

namespace Tok
  public export
  pure : a -> Tok False e a
  pure v cs = Succ v cs

  public export
  (>>=) : Tok b1 e a -> (a -> Tok b2 e b) -> Tok (b1 || b2) e b
  (>>=) f g cs =
    let Succ x cs1 @{q} := f cs    | Fail x y z => Fail x y z
     in swapOr $ trans (g x cs1) q

  public export
  (>>) : Tok b1 e () -> Tok b2 e a -> Tok (b1 || b2) e a
  (>>) f g cs =
    let Succ _ cs1 @{q} := f cs | Fail x y z => Fail x y z
     in swapOr $ trans (g cs1) q

  public export
  (*>) : Tok b1 e a -> Tok b2 e b -> Tok (b1 || b2) e b
  (*>) f g cs =
    let Succ _ cs1 @{q} := f cs | Fail x y z => Fail x y z
     in swapOr $ trans (g cs1) q

  public export
  (<*) : Tok b1 e a -> Tok b2 e b -> Tok (b1 || b2) e a
  (<*) f g cs =
    let Succ v cs1 @{q1} := f cs  | Fail x y z => Fail x y z
        Succ _ cs2 @{q2} := g cs1 | Fail x y z => Fail (weaken $ trans x q1) y z
     in Succ v cs2 @{swapOr $ trans q2 q1}

  public export
  (<*>) : Tok b1 e (a -> b) -> Tok b2 e a -> Tok (b1 || b2) e b
  (<*>) t1 t2 cs =
    let Succ fun cs1 @{q} := t1 cs  | Fail x y z => Fail x y z
        Succ val cs2 @{r} := t2 cs1 | Fail r y z => Fail (weaken $ trans r q) y z
     in Succ (fun val) cs2 @{swapOr $ trans r q}

namespace AutoTok

  public export
  pure : a -> AutoTok e a
  pure v cs = Succ v cs

  public export
  (<*>) : AutoTok e (a -> b) -> AutoTok e a -> AutoTok e b
  (<*>) t1 t2 cs =
    let Succ fun cs1 := t1 cs  | Fail x y z => Fail x y z
        Succ val cs2 := t2 cs1 | Fail x y z => Fail x y z
     in Succ (fun val) cs2

  public export
  (<*) : AutoTok e a -> AutoTok e b -> AutoTok e a
  (<*) t1 t2 cs =
    let Succ val cs1 := t1 cs  | Fail x y z => Fail x y z
        Succ _   cs2 := t2 cs1 | Fail x y z => Fail x y z
     in Succ val cs2

  public export
  (>>=) : AutoTok e a -> (a -> AutoTok e b) -> AutoTok e b
  (>>=) f g cs =
    let Succ x cs1 := f cs | Fail x y z => Fail x y z
     in g x cs1

  public export
  (>>) : AutoTok e () -> AutoTok e a -> AutoTok e a
  (>>) f g cs =
    let Succ _ cs1 := f cs | Fail x y z => Fail x y z
     in g cs1

  public export
  (*>) : AutoTok e a -> AutoTok e b -> AutoTok e b
  (*>) f g cs =
    let Succ _ cs1 := f cs | Fail x y z => Fail x y z
     in g cs1
