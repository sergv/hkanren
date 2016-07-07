# HKanren

Successor of ds-kanren that provides more typeful logic programming environment
in the spirit of Haskell.

This project is in a prototype stage - a work in progress for the time being.

The aim is to write [miniKanren](http://minikanren.org) programs in Haskell as
a DSL.

The distictive feature of this project is to ensure that these programs are well-typed.
This was achieved by requiring all logic variables to be typed.

If you're interested, check out programs in this DSL for [natural numbers](src/Language/HKanren/Functions/Nat.hs) (duh) and [lists](src/Language/HKanren/Functions/List.hs) (more exciting).
