# idris2-parser: Total Lexers and Parsers for Idris2

This is a library for writing provably total lexers and parsers
in the Idris programming language. While it provides a domain specific
language (DSL) of combinators similar to what can be found in the
*contrib* library and the Idris compiler API, it's main focus lies
on making the manual writing of lexers and parsers as nice as possible.

There are several advantages to not using a combinator library and
using explicit mutual recursion instead:

* Performance can easily improve by an order of magnitude
* Perfect control over the errors our parsers throw and when they are
  being thrown
* The code is not necessarily more obfuscated

A [tutorial](docs/src/Intro.md) is in the making where the points above
will be addressed.

## parser-toml

The parser-toml sub-project provides a feature-complete, total lexer
and parser for the [TOML config file format](https://toml.io/en/)
implemented manually using the techniques described in the tutorial.

## parser-json

This sub-project provides a lexer and parser for the
[JSON file format](https://en.wikipedia.org/wiki/JSON). They will eventually
replace the lexer and parser currently used in
[idris2-json](https://github.com/stefan-hoeck/idris2-json).

