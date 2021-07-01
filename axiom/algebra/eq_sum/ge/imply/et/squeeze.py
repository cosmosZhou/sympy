from util import *


@apply
def apply(eq, ge):
    if ge.is_Equal:
        eq, ge = ge, eq
        
    (xi, (i, _0, n)), a = eq.of(Equal[Sum])
    xn, _a = ge.of(GreaterEqual)
    assert a == _a

    assert n > 0
    assert xn == xi._subs(i, n - 1)

    return Equal(xn, a), All[i:n - 1](Equal(xi, 0))


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol.x(real=True, negative=False, shape=(oo,), given=True)
    n = Symbol.n(integer=True, negative=False, given=True)
    i = Symbol.i(integer=True)
    a = Symbol.a(real=True, negative=False)
    Eq << apply(Equal(Sum[i:n + 1](x[i]), a), x[n] >= a)

    Eq.eq = Eq[0].this.lhs.apply(algebra.sum.to.add.split, cond={n})

    Eq << GreaterEqual(Eq.eq.find(Sum), 0, plausible=True)

    Eq << algebra.eq.ge.imply.le.sub.apply(Eq.eq, Eq[-1])

    Eq << algebra.ge.le.imply.eq.apply(Eq[1], Eq[-1])

    Eq << Eq.eq.subs(Eq[2]).this.apply(algebra.eq.simplify.terms.common)

    j = Symbol.j(integer=True)
    Eq << Eq[-1].this.lhs.limits_subs(i, j)

    Eq << ~Eq[3]

    Eq << Eq[-1].this.function.apply(algebra.is_nonzero.imply.is_positive)

    Eq << Eq[-3].this.lhs.apply(algebra.sum.to.add.split, cond={i})

    Eq << algebra.cond.any.imply.any_et.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this().function.find(Piecewise, Contains).simplify()

    Eq << Eq[-1].this.function.apply(algebra.eq.gt.imply.lt.sub)


if __name__ == '__main__':
    run()