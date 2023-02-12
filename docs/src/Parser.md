# Parsing Arithmetic Expressions

In this section, we are going to parse the tokens generated
in the [previous section](Intro.md) and convert them to proper
arithmetic expressions.

```idris
module Parser

import Intro
import Text.Parse.Manual

%default total
```

## A Chain of Infix Operators

Before we actually implement the parser proper, we have to quickly
discuss, how we are going to handle operator precedence in chains
of infix operators without parentheses. For instance, the expression
`1 * 2 + 3 * 4` should be parsed as `(1 * 2) + (3 * 4)` an not as
`1 * (2 + (3 * 4))`, which might be more straightforward when parsing
the expression from left to right. Our parse should convert such
operator chains in to `SnocList` of pairs, with the final expression
given separately. This can then be converted conveniently using the following
recursive function:

```idris
opChain : SnocList (Expr,Op) -> Expr -> Expr
opChain [<]           x = x
opChain (sx :< (y,P)) x = opChain sx y + x
opChain (sx :< (y,M)) x = opChain sx (y * x)
```

So, in case of a plus operator (`+`), we first evaluate the
remainder of the operator chain before adding it to the current
expression. In case of multiplication, we multiply the
two neighbouring expressions before moving on. This guarantees,
that multiplication will have the higher precedence than addition.

## Parsing a Sequence of Tokens

We first define a type alias for a parsing rule. The boolean flag
indicates, whether we are talking about a *strict* rule, guaranteed
to consume some input. As with the provably total lexer, we
use a value of type `SuffixAcc` as a witness that the parser must
terminate in a finite number of steps.

```idris
0 Rule : Bool -> Type -> Type
Rule b t =
     (xs : List $ Bounded Token)
  -> (0 acc : SuffixAcc xs)
  -> Res b Token xs Void t
```

One note about the `Void` in the type above: The `ParseError` type
of this library has support for custom errors, which we are not going
to need here. We therefore set the custom error type to `Void`.

An *applied expression* is either a literal, a complex expression wrapped
in parentheses. An expression is a
a chain of one or more applied expressions linked via infix operators.
Here are the necessary mutually recursive functions require to
express this:

```idris
ops : Expr -> SnocList (Expr,Op) -> Rule False Expr

applied,expr : Rule True Expr

applied (B '(' b :: xs) (SA r) = case succ $ expr xs r of
  Res.Succ v (B ')' _ :: xs) => Succ v xs
  res                        => failInParen b '(' res
applied (B (TLit n) _ :: xs) _ = Succ (Lit n) xs
applied xs                   _ = fail xs

expr xs acc@(SA r) = case applied xs acc of
  Succ v ys => succ $ ops v [<] ys r
  Fail err  => Fail err

ops x sp (B (TOp o) _ :: xs) (SA r) = case succ $ applied xs r of
  Res.Succ v ys => wsucc $ ops v (sp :< (x,o)) ys r
  Fail err                   => Fail err
ops x sp xs _ = Succ (opChain sp x) xs
```

And that's it. The utilities used above come from module `Text.Parser.Res`,
and we are going to have closer look at some of them. First, as with the
lexer we wrote in the previous section, `Res` is a type with the potential
of failure, which holds a proof that the wrapped list is a suffix
of the original list. The boolean flag indicates, whether the suffix is
strict or not. We can only use strict `Rule`s in arbitrary recursive
functions.

```idris
parseExpr : Origin -> String -> Either (FileContext,Err) Expr
parseExpr o str = case toks4 str of
  Left err => Left $ fromBounded o err
  Right ts => result o $ expr ts suffixAcc

parseAndPrint : String -> IO ()
parseAndPrint s = putStrLn $ either (uncurry $ printParseError s) show (parseExpr Virtual s)
```

<!-- vi: filetype=idris2:syntax=markdown
-->
