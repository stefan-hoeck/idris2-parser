# idris2-parser: Total Lexers and Parsers for Idris2

This is a library for writing provably total lexers and parsers
in the Idris programming language. While it provides a domain specific
language (DSL) of combinators similar to what can be found in the
*contrib* library and the Idris compiler API, it's main focus lies
on making the manual writing of lexers and parsers as nice as possible.

There are several advantages to not using a combinator library and
using explicit mutual recursion instead:

  * Performance can easily improved by an order of magnitude, 
  * We get perfect control over the errors our parsers throw
  * The code is not necessarily more obfuscated

A [tutorial](docs/src/Intro.md) is the making where the points above
will be addressed.
