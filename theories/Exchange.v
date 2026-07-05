(**
  Facade for exchange matching, opening auctions, and multi-leg strategies.

  The underlying prototype contains admitted declarations.  It is exposed
  under [Experimental] so those results cannot be mistaken for the
  assumption-free core of the library.
*)

From Top Require Import OptionMatchingPrototype.

Module Experimental := Top.OptionMatchingPrototype.
