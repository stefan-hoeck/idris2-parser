module Text.WebIDL.Parser.Arguments

import Text.WebIDL.Parser.Attributes
import Text.WebIDL.Parser.Type
import Text.WebIDL.Parser.Util

%default total

constValue : Rule True ConstValue
constValue (B (FLit x) _ :: xs) = Succ0 (F x) xs
constValue (B (ILit x) _ :: xs) = Succ0 (I x) xs
constValue (B "true"   _ :: xs) = Succ0 (B True) xs
constValue (B "false"  _ :: xs) = Succ0 (B False) xs
constValue xs                   = fail xs

defaultV : Rule False Default
defaultV (B '=' _ :: B '[' _ :: B ']' _ :: xs) = Succ0 EmptyList xs
defaultV (B '=' _ :: B '{' _ :: B '}' _ :: xs) = Succ0 EmptySet xs
defaultV (B '=' _ :: B "null" _         :: xs) = Succ0 Null xs
defaultV (B '=' _ :: B (SLit x) _       :: xs) = Succ0 (S x) xs
defaultV (B '=' _                       :: xs) = succF $ C <$> constValue xs
defaultV xs                                    = Succ0 None xs

argName : Rule True ArgumentName
argName (B (Ident s) b :: xs) = case refineArgumentNameKeyword s.value of
  Just nm => Succ0 (MkArgName nm.value) xs
  Nothing => Succ0 (MkArgName s.value) xs
argName xs = fail xs

ellipsis : Rule False Bool
ellipsis (B (Other Ellipsis) _ :: xs) = Succ0 True xs
ellipsis xs                           = Succ0 False xs

args : Bounds -> SnocList Arg -> SnocList OptArg -> AccRule True ArgumentList
args b sa so xs (SA r) = case attributes xs of
  Succ0 as1 (B "optional" _ :: r1) =>
    let Succ0 as2 r2 := attributes r1        | Fail0 e => Fail0 e
        Succ0 tpe r3 := idlType r2 suffixAcc | Fail0 e => Fail0 e
        Succ0 arg r4 := argName r3           | Fail0 e => Fail0 e
        Succ0 def r5 := defaultV r4          | Fail0 e => Fail0 e
        newArg       := MkOptArg as1 as2 tpe arg def

        -- proof of type `Suffix True r5 xs`
        0 p          := strict {ys = xs} [F r5, T r4,T r3,F r2,F r1]
    in case r5 of
         B ',' _ :: r6 => succT (args b sa (so :< newArg) r6 r) --continue after ','
         _             => Succ0 (NoVarArg (sa <>> []) (so <>> [newArg])) r5

  Succ0 as1 r1                     => case so of
    -- interleaving of optional an regular args makes no sense
    (_ :< _) => case r1 of
      []   => unclosed b '('
      x::_ => expected x.bounds "optional"

    -- no optional args so far, so regular arg is fine
    [<] =>
      let Succ0 tpe  r2 := idlType r1 suffixAcc | Fail0 e => Fail0 e
          Succ0 boo  r3 := ellipsis r2          | Fail0 e => Fail0 e
          Succ0 arg  r4 := argName r3           | Fail0 e => Fail0 e
          newArg        := MkArg as1 tpe arg

          -- proof of type `Suffix True r4 xs`
          0 p           := strict {ys = xs} [T r4,F r3,T r2,F r1]
       in if boo then Succ0 (VarArg (sa <>> []) newArg) r4 -- stop after vararg
          else case r4 of
            B ',' _ :: r5 => succT (args b (sa :< newArg) so r5 r) --continue after ','
            _             => Succ0 (NoVarArg (sa <>> [newArg]) (so <>> [])) r4
  res => failInParen b '(' res
              
export
argumentList : Rule True ArgumentList
argumentList (B '(' _ :: B ')' _ :: xs) = Succ0 (NoVarArg Nil Nil) xs
argumentList (B '(' b :: xs) = case succT $ args b [<] [<] xs suffixAcc of
  Succ0 as (B ')' _ :: xs) => Succ0 as xs
  res                      => failInParen b '(' res
argumentList (x::xs) = expected x.bounds '('
argumentList []      = eoi
