module Text.WebIDL.Types.Argument

import Data.Bitraversable
import Data.Traversable
import Derive.Prelude
import Text.WebIDL.Types.Attribute
import Text.WebIDL.Types.Identifier
import Text.WebIDL.Types.Numbers
import Text.WebIDL.Types.StringLit
import Text.WebIDL.Types.Type

%language ElabReflection

||| ConstValue ::
|||     BooleanLiteral
|||     FloatLiteral
|||     integer
|||
||| BooleanLiteral ::
|||     true
|||     false
public export
data ConstValue = B Bool | F FloatLit | I IntLit

%runElab derive "ConstValue" [Eq,Show,HasAttributes]

||| Default ::
|||     = DefaultValue
|||     ε
|||
||| (part of Default)] DefaultValue ::
|||     ConstValue
|||     string
|||     [ ]
|||     { }
|||     null
public export
data Default = None
             | EmptyList
             | EmptySet
             | Null
             | S StringLit
             | C ConstValue

%runElab derive "Default" [Eq,Show,HasAttributes]

||| ArgumentName ::
|||     ArgumentNameKeyword
|||     identifier
public export
record ArgumentName where
  constructor MkArgName
  value : String

%runElab derive "ArgumentName" [Eq,Show,HasAttributes]

public export
record ArgF (a : Type) (b : Type) where
  constructor MkArg
  attrs    : a
  type     : IdlTypeF a b
  name     : ArgumentName

%runElab derive "ArgF" [Eq,Show]

public export
Arg : Type
Arg = ArgF ExtAttributeList Identifier

public export
record OptArgF (a : Type) (b : Type) where
  constructor MkOptArg
  attrs     : a
  typeAttrs : a
  type      : IdlTypeF a b
  name      : ArgumentName
  def       : Default

%runElab derive "OptArgF" [Eq,Show]

public export
OptArg : Type
OptArg = OptArgF ExtAttributeList Identifier

||| ArgumentList ::
|||     Argument Arguments
|||     ε
|||
||| Arguments ::
|||     , Argument Arguments
|||     ε
|||
||| Argument ::
|||     ExtendedAttributeList ArgumentRest
|||
||| Ellipsis ::
|||     ...
|||     ε
||| ArgumentRest ::
|||     optional TypeWithExtendedAttributes ArgumentName Default
|||     Type Ellipsis ArgumentName
public export
data ArgumentListF : (a : Type) -> (b : Type) -> Type where
  VarArg :  (args : List $ ArgF a b)
         -> (vararg : ArgF a b)
         -> ArgumentListF a b

  NoVarArg :  (args : List $ ArgF a b)
           -> (optArgs : List $ OptArgF a b)
           -> ArgumentListF a b

%runElab derive "ArgumentListF" [Eq,Show]

public export
ArgumentList : Type
ArgumentList = ArgumentListF ExtAttributeList Identifier

--------------------------------------------------------------------------------
--          Implementations
--------------------------------------------------------------------------------

mutual
  export
  Bifunctor ArgF where bimap = assert_total bimapDefault

  export
  Bifoldable ArgF where bifoldr = bifoldrDefault

  export
  Bitraversable ArgF where
    bitraverse f g (MkArg a t n) =
      [| MkArg (f a) (bitraverse f g t) (pure n) |]

  export
  Functor (ArgF a) where map = bimap id

  export
  Foldable (ArgF a) where foldr = bifoldr (const id)

  export
  Traversable (ArgF a) where traverse = bitraverse pure

mutual
  export
  Bifunctor OptArgF where bimap = assert_total bimapDefault

  export
  Bifoldable OptArgF where bifoldr = bifoldrDefault

  export
  Bitraversable OptArgF where
    bitraverse f g (MkOptArg a1 a2 t n d) =
      [| MkOptArg (f a1) (f a2) (bitraverse f g t) (pure n) (pure d) |]

  export
  Functor (OptArgF a) where map = bimap id

  export
  Foldable (OptArgF a) where foldr = bifoldr (const id)

  export
  Traversable (OptArgF a) where traverse = bitraverse pure

mutual
  export
  Bifunctor ArgumentListF where bimap = assert_total bimapDefault

  export
  Bifoldable ArgumentListF where bifoldr = bifoldrDefault

  export
  Bitraversable ArgumentListF where
    bitraverse f g (VarArg as a) =
      [| VarArg (traverse (bitraverse f g) as) (bitraverse f g a) |]
    bitraverse f g (NoVarArg as os) =
      [| NoVarArg (traverse (bitraverse f g) as) (traverse (bitraverse f g) os) |]

  export
  Functor (ArgumentListF a) where map = bimap id

  export
  Foldable (ArgumentListF a) where foldr = bifoldr (const id)

  export
  Traversable (ArgumentListF a) where traverse = bitraverse pure

  export
  HasAttributes a => HasAttributes (ArgumentListF a b) where
    attributes = bifoldMap attributes (const Nil)
