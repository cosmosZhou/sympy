from util import *


@apply
def apply(given):
    x, S = given.of(Contains)
    function, *limits = S.of(Cap)

    for v in S.variables:
        if x._has(v):
            _v = v.generate_var(given.free_symbols, **v.type.dict)
            S = S.limits_subs(v, _v)

    contains = Contains(x, S.function).simplify()
    return All(contains, *S.limits)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(positive=True, integer=True, given=True)
    x = Symbol.x(integer=True, given=True)
    k = Symbol.k(integer=True)

    A = Symbol.A(shape=(oo,), etype=dtype.integer, given=True)

    Eq << apply(Contains(x, Cap[k:n](A[k])))

    k = Symbol.k(domain=Range(0, n))

    Eq << Eq[0].this.rhs.split({k})

    Eq << sets.contains.imply.contains.split.intersection.apply(Eq[-1], index=0)

    Eq << Eq[-1].forall((k,))


if __name__ == '__main__':
    run()

