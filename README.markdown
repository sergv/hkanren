## DS-Kanren
A subset implementation of the already small logical language!
ds-kanren provides a simple way to write logical relations and queries
in Haskell.

The language supports

 - `conde`
 - `===`
 - `=/=`

As a brief demonstration, the classic `appendo` relation.

``` haskell
appendo :: Term -> Term -> Term -> Predicate
appendo l r o =
  conde [ program [l === "nil", o === r]
        , manyFresh $ \h t o' ->
            program [ Pair h t === l
                    , appendo t r o'
                    , Pair h o' === o ]]
```

Which is just a normal Haskell function mapping 3 `Term`s to a
`Predicate`. From here we can run a few different ways

    >>> let l = list ["foo", "bar"]
    .
    >>> map fst . runN 1 $ \t -> appendo t l l
    [nil]
    >>> map fst . runN 1 $ \t -> appendo l t l
    [nil]
    >>> map fst . runN 1 $ \t -> appendo l l t
    [(foo, (bar, (foo, (bar, nil))))]

`run` returns a list of solutions and inequality constraints. The
inequality constraints are things generated from `=/=`'s. Some of
these might be redundant but none of them will be incorrect.

## Related Links

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
