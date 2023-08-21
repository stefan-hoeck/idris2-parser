module Text.WebIDL.Parser.Arguments

import Text.WebIDL.Parser.Attributes
import Text.WebIDL.Parser.Type
import Text.WebIDL.Parser.Util
import Text.Parse.Syntax

%hide Prelude.(<*>)
%hide Prelude.(*>)
%hide Prelude.(<*)
%hide Prelude.pure

%default total

export
constValue : Rule True ConstValue
constValue (B (FLit x) _ :: xs) = Succ0 (F x) xs
constValue (B (ILit x) _ :: xs) = Succ0 (I x) xs
constValue (B "true"   _ :: xs) = Succ0 (B True) xs
constValue (B "false"  _ :: xs) = Succ0 (B False) xs
constValue xs                   = fail xs

export
defaultV : Rule False Default
defaultV (B '=' _ :: B '[' _ :: B ']' _ :: xs) = Succ0 EmptyList xs
defaultV (B '=' _ :: B '{' _ :: B '}' _ :: xs) = Succ0 EmptySet xs
defaultV (B '=' _ :: B "null" _         :: xs) = Succ0 Null xs
defaultV (B '=' _ :: B (SLit x) _       :: xs) = Succ0 (S x) xs
defaultV (B '=' _                       :: xs) = succF $ C <$> constValue xs
defaultV xs                                    = Succ0 None xs

argName : Rule True ArgumentName
argName (B (Key s) b :: xs) = case refineArgumentNameKeyword s.value of
  Just nm => Succ0 (MkArgName nm.value) xs
  Nothing => custom b (InvalidArgName s.value)
argName (B (Ident s) b :: xs) = Succ0 (MkArgName s.value) xs
argName xs = fail xs

ellipsis : Rule False Bool
ellipsis (B (Other Ellipsis) _ :: xs) = Succ0 True xs
ellipsis xs                           = Succ0 False xs

export
arg : ExtAttributeList -> Rule True (Bool,Arg)
arg as = [| toArg idlType ellipsis argName |]

  where
    toArg : IdlType -> Bool -> ArgumentName -> (Bool,Arg)
    toArg t b a = (b, MkArg as t a)

optArg : ExtAttributeList -> Rule True OptArg
optArg as = [| MkOptArg (pure as) attributes idlType argName defaultV |]

-- this comes after we checked for empty arg lists or the presence of
-- a comma, so it must consume at least one more argument
args : SnocList Arg -> SnocList OptArg -> AccRule True ArgumentList
args sa so xs (SA r) = case attributes xs of
  Succ0 as1 (B "optional" _ :: r1) => case succT $ optArg as1 r1 of
    Succ0 o (B ',' _ :: r2) => succT (args sa (so :< o) r2 r)
    Succ0 o r2              => Succ0 (NoVarArg (sa <>> []) (so <>> [o])) r2
    Fail0 err               => Fail0 err

  Succ0 as1 r1 @{p} => case so of
    -- interleaving of optional and regular args makes no sense
    (_ :< _) => case r1 of
      []   => eoi
      x::_ => expected x.bounds "optional"

    -- no optional args so far, so regular arg is fine
    [<] => case trans (arg as1 r1) p of
      Succ0 (True,a) r2           => Succ0 (VarArg (sa <>> []) a) r2
      Succ0 (_,a) (B ',' _ :: r2) => succT (args (sa :< a) so r2 r)
      Succ0 (_,a) r2              => Succ0 (NoVarArg (sa <>> [a]) []) r2
      Fail0 err                   => Fail0 err
  Fail0 err => Fail0 err
              
export
argumentList : Rule True ArgumentList
argumentList (B '(' _ :: B ')' _ :: xs) = Succ0 (NoVarArg Nil Nil) xs
argumentList xs = between '(' ')' (acc $ args [<] [<]) xs
              
export
optArgList : Rule False ArgumentList
optArgList (B '(' b :: xs) =
  weaken $ argumentList (B (Other $ Symb '(') b :: xs)
optArgList xs = Succ0 (NoVarArg Nil Nil) xs
