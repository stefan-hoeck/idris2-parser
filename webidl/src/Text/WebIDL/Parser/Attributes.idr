module Text.WebIDL.Parser.Attributes

import Text.WebIDL.Parser.Util

%default total

--------------------------------------------------------------------------------
--          Extended Attributes
--------------------------------------------------------------------------------

isOpen : IdlToken -> Bool
isOpen '(' = True
isOpen '[' = True
isOpen '{' = True
isOpen _   = False

closes : IdlToken -> IdlToken -> Bool
')' `closes` '(' = True
']' `closes` '[' = True
'}' `closes` '{' = True
_   `closes` _   = False

toOther : IdlToken -> Maybe Other
toOther (SLit x)         = Just $ inject x
toOther (ILit x)         = Just $ inject x
toOther (FLit x)         = Just $ inject x
toOther (Ident x)        = Just $ inject x
toOther (Key x)          = Just $ inject x
toOther (Other Ellipsis) = Just $ inject Ellipsis
toOther (Other (Symb c)) =
  if isCommaOrParenOrQuote c then Nothing else Just $ inject (Symb c)
toOther _                = Nothing

innerOrOther : AccRule True InnerOrOther

-- ExtendedAttributeInner ::
--     ( ExtendedAttributeInner ) ExtendedAttributeInner
--     [ ExtendedAttributeInner ] ExtendedAttributeInner
--     { ExtendedAttributeInner } ExtendedAttributeInner
--     OtherOrComma ExtendedAttributeInner
--     ε
eaInner : SnocList InnerOrOther -> AccRule False EAInner
eaInner sx (B ',' b :: xs) (SA r) =
  succF $ eaInner (sx :< Right (inject (Symb ','))) xs r
eaInner sx xs acc@(SA r) = case innerOrOther xs acc of
  Succ0 io ys => succF $ eaInner (sx :< io) ys r
  Fail0 _     => Succ0 (innerAttribute sx []) xs

innerOrOther (B t b :: xs) (SA r) =
  if isOpen t then case succT $ eaInner [<] xs r of
    Succ0 v (B c b2 :: ys) =>
      if c `closes` t then Succ0 (Left v) ys else unexpected (B c b2)
    res => failInParen b t res
  else case toOther t of
    Just o  => Succ0 (Right o) xs
    Nothing => unexpected (B t b)
innerOrOther [] _ = eoi

-- ExtendedAttributeRest ::
--     ExtendedAttribute
--     ε
eaRest : SnocList InnerOrOther -> InnerOrOther -> AccRule False ExtAttribute
eaRest sx x ts acc@(SA r) = case innerOrOther ts acc of
  Succ0 e ys => succF $ eaRest (sx :< x) e ys r
  _          => Succ0 (extAttribute sx $ Last x) ts

-- ExtendedAttribute ::
--     ( ExtendedAttributeInner ) ExtendedAttributeRest
--     [ ExtendedAttributeInner ] ExtendedAttributeRest
--     { ExtendedAttributeInner } ExtendedAttributeRest
--     Other ExtendedAttributeRest
ea : Rule True ExtAttribute
ea xs = case innerOrOther xs suffixAcc of
  Succ0 e ys => succT $ eaRest [<] e ys suffixAcc
  Fail0 err  => Fail0 err

-- ExtendedAttributes ::
--     , ExtendedAttribute ExtendedAttributes
--     ε
eas : SnocList ExtAttribute -> Bounds -> AccRule True ExtAttributeList
eas sa b ts (SA r) = case ea ts of
  Succ0 v (B ']' _ :: xs) => Succ0 (sa <>> [v]) xs
  Succ0 v (B ',' _ :: xs) => succT $ eas (sa :< v) b xs r
  res                     => failInParen b '[' res

-- ExtendedAttributeList ::
--     [ ExtendedAttribute ExtendedAttributes ]
--     ε
export
attributes : Rule False ExtAttributeList
attributes (B '[' b :: xs) = succF $ eas [<] b xs suffixAcc
attributes xs              = Succ0 [] xs
