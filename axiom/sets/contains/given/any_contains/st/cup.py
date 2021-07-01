from util import *


@apply
def apply(imply):
    x, S = imply.of(Contains)
    function, *limits = S.of(Cup)

    for v in S.variables:
        if x._has(v):
            _v = v.generate_var(imply.free_symbols, **v.type.dict)
            S = S.limits_subs(v, _v)

    contains = Contains(x, S.function).simplify()
    return Any(contains, *S.limits)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(positive=True, integer=True)
    x = Symbol.x(integer=True)
    k = Symbol.k(integer=True)

    A = Symbol.A(shape=(oo,), etype=dtype.integer)

    Eq << apply(Contains(x, Cup[k:n](A[k])))

    i = Symbol.i(domain=Range(0, n))
    Eq << Eq[-1].limits_subs(k, i)

    Eq << Subset(A[i], Eq[0].rhs, plausible=True)
    Eq << Eq[-1].this.rhs.split(i.set)

    Eq << Eq[-2].this.function.apply(sets.contains.subset.imply.contains, Eq[-1])


if __name__ == '__main__':
    run()

