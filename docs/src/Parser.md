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
operator chains to a `SnocList` of pairs, with the final expression
given separately. This can then be converted conveniently using the
following recursive function:

```idris
opChain : SnocList (Expr,Op) -> Expr -> Expr
opChain [<]           x = x
opChain (sx :< (y,A)) x = opChain sx y + x
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
terminate in a finite number of steps. We will need this, since
our rules are going to be mutually recursive.

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

An *applied expression* is either a literal or a composite expression
wrapped in parentheses: An *expression* is
a chain of one or more applied expressions linked via infix operators.
Here are the necessary mutually recursive functions require to
express this:

```idris
ops : Expr -> SnocList (Expr,Op) -> Rule False Expr

applied,expr : Rule True Expr

applied (B (TLit n) _ :: xs) _ = Succ (Lit n) xs
applied (B '(' b :: xs) (SA r) = case succ $ expr xs r of
  Res.Succ v (B ')' _ :: xs) => Succ v xs
  res                        => failInParen b '(' res
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
and we are going to have a closer look at some of them. First, as with the
lexer we wrote in the previous section, `Res` is a type with the possibility
of failure, which holds a proof that the wrapped list is a suffix
of the original list in case of a success. The boolean flag indicates,
whether the suffix is strict or not.

Let's have a closer look at the implementation of `applied`: As usual,
we use pattern matching to look at the prefix of the list of tokens.
In case of an opening parenthesis, we invoke `expr` recursively.
This is guaranteed to terminated since `xs` is a strict suffix of the
input list, which is obvious for Idris in this case, but is also witnessed
by `r`, the inner function of the current `SuffixAcc`.

Note the call to `succ`: If we just invoke `expr xs r`, the result will
be of type `Res True Token xs Void Expr`. But our result will have to
be of type `Res True Token (B '(' _ :: xs) Void Expr`. Function `succ`
will adjust the proof for us (go, an checkout its type and implementation).
Since it only modifies the erased `Suffix` proof, it is the identity
function at runtime and will be optimized away.

After parsing the expression, we check that the parenthesis has been
properly close, otherwise `applied` fails with an error.

The other two rules are implemented in a similar fashion. Rule `ops`
accumulates some state, so it has a slightly more complex function signature.
With the following `IO` action, we can try out the parser at the REPL:

```idris
parseExpr : Origin -> String -> Either (FileContext,Err) Expr
parseExpr o str = case toks4 str of
  Left err => Left $ fromBounded o err
  Right ts => result o $ expr ts suffixAcc

parseAndPrint : String -> IO ()
parseAndPrint s =
  putStrLn $ either (uncurry $ printParseError s) show (parseExpr Virtual s)
```

And here is an example REPL session:

```repl
Parser> :exec parseAndPrint "12 + 2 * 3"
Add (Lit 12) (Mult (Lit 2) (Lit 3))
Parser> :exec parseAndPrint "(12 + 2) * 3"
Mult (Add (Lit 12) (Lit 2)) (Lit 3)
Parser> :exec parseAndPrint "(12 + 2 * 3"
Error: Unclosed '('

virtual: 1:1--1:2
 1 | (12 + 2 * 3
     ^

Parser> :exec parseAndPrint "(12 + 2 * 3) +"
Error: End of input

Parser> :exec parseAndPrint "(12 + 2 * 3) + )"
Error: Unexpected ')'

virtual: 1:16--1:17
 1 | (12 + 2 * 3) + )
                    ^
```

As you can see, we get clear and pretty error messages pointing
exactly at the culprit in case of a parse error. The only not so nice part:
No text position is printed in the `End of input` case. This can be
fixed by specifying an `EndOfInput` token and manually appending it
to the list of tokens during lexing. We will look at this technique
in a later section.

## Conclusion and next Steps

This concludes this introduction about manually writing a parser
for arithmetic expressions. Depending on your background, you might find
the idea of manually writing a lexer and parser quite horrible. What
about the nice combinator libraries we are used to when working
with functional programming languages? Well, we are going to look
at those in the next section.

<!-- vi: filetype=idris2:syntax=markdown
-->
