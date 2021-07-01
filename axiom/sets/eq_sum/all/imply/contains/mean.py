from util import *


@apply
def apply(eq, all):
    if eq.is_All:
        eq, all = all, eq
    wi, (i, n) = eq.of(Equal[Sum[Tuple[0]], 1])
    (_wi, (xi, domain)), (_i, _n) = all.of(All[And[Expr >= 0, Contains], Tuple[0]])
    assert i == _i and _n == n
    assert _wi == wi    
    
    return Contains(Sum[i:n](wi * xi), domain)

@prove
def prove(Eq):
    from axiom import sets, algebra

    i = Symbol.i(integer=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    w = Symbol.w(real=True, shape=(oo,))
    x = Symbol.x(real=True, shape=(oo,))
    Eq << apply(Equal(Sum[i:n](w[i]), 1), All[i:n]((w[i] >= 0) & Contains(x[i], Interval(a, b))))

    Eq << sets.imply.suffice.contains.interval.apply(Eq[1].find(Contains), w=w[:n])

    Eq <<= Eq[0] & Eq[1]

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()