from util import *


@apply
def apply(given):
    x, S = given.of(Element)
    function, *limits = S.of(Cup)

    for v in S.variables:
        if x._has(v):
            _v = v.generate_var(given.free_symbols, **v.type.dict)
            S = S.limits_subs(v, _v)

    contains = Element(x, S.expr).simplify()
    return Any(contains, *S.limits)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(positive=True, integer=True, given=True)
    x = Symbol(integer=True, given=True)
    k = Symbol(integer=True)

    A = Symbol(shape=(oo,), etype=dtype.integer, given=True)

    Eq << apply(Element(x, Cup[k:n](A[k])))

    Eq << ~Eq[1]

    Eq << sets.all_notin.imply.notin.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

