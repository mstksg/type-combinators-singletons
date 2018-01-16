type-combinator-singletons
==========================

Conversions between data-types in *[type-combinators][]* and singletons from
*[singletons][]* and orphan instances.

[type-combinators]: https://hackage.haskell.org/package/type-combinators
[singletons]: https://hackage.haskell.org/package/singletons

There's a lot of overlap in functionality between the two libraries.  I often
use both of them together side-by-side to do different things, but there is
some friction the process of converting between the identical data types that
both libraries have, and between similar typeclasses.  This library attempts to
ease that friction by providing conversion functions between identical data
types and also many of the appropriate orphan typeclass instances.
