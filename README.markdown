## DS-Kanren
A subset implementation of the already small logical language!
ds-kanren provides a simple way to write logical relations and queries
in Haskell.

The language supports

 - `conde`
 - `===`
 - `suco` (The successor relation)
 - `=/=`

As a brief demonstration, the classic `appendo` relation.

``` haskell
    appendo :: Term -> Term -> Term -> Predicate
    appendo l r o =
      conde [ program [l === Integer 0,  o === r]
            , manyFresh $ \h t o' ->
                program [ Pair h t === l
                        , appendo t r o'
                        , Pair h o' === o ]]
```

Which is just a normal Haskell function mapping 3 `Term`s to a
`Predicate`. From here we can run a few different ways

``` haskell
    λ> run1 $ \t -> appendo t (term [1, 2, 3]) (term [1, 2, 3])
    Integer 0 -- We treat Integer 0 as Nil of our lists
    λ> run1 $ \t -> appendo (term [1, 2, 3]) t (term [1, 2, 3])
    Integer 0
    λ> run $ \t -> appendo (term [1, 2, 3]) (term [1, 2, 3]) t
    [Pair (Integer 1) (Pair (Integer 2) (Pair (Integer 3)
    (Pair (Integer 1) (Pair (Integer 2) (Pair (Integer 3) (Integer 0))))))]
```

Some good places to start learning about miniKanren would be

 - [The Reasoned Schemer][reasoned]
 - [William and Daniel's presentation at StrangeLoop][slpresi]
 - [The canonical implementation][canonimpl]

For this implementation in particular, it may be helpful to look at my
[blog post][post] explaining `Logic` monad.

[reasoned]: http://www.amazon.com/The-Reasoned-Schemer-Daniel-Friedman/DP/0262562146
[slpresi]: http://www.infoq.com/presentations/miniKanren
[canonimpl]: https://github.com/miniKanren/miniKanren
[post]: http://jozefg.bitbucket.org/posts/2014-07-10-reading-logict.html
