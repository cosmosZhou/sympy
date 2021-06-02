from util import *
import axiom



@apply
def apply(*given, n=None, start=0):
    start = sympify(start)
    f0, sufficient = given
    f0.of(Contains)

    fn, fn1 = sufficient.of(Suffice)
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, start) == f0
    assert n.domain.min() == start

    return fn


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo,))
    g = Symbol.g(etype=dtype.integer, shape=(oo,))

    Eq << apply(Contains(f[0], g[0]), Suffice(Contains(f[n], g[n]), Contains(f[n + 1], g[n + 1])), n=n)

    h = Symbol.h(Lamda[n](Bool(Contains(f[n], g[n]))))

    Eq << h[0].this.definition

    Eq << sets.contains.imply.eq.bool.contains.apply(Eq[0])

    Eq << Eq[-1] + Eq[-2]

    Eq.equality = Eq[-1].this.apply(algebra.eq.simplify.terms.common)

    Eq.suffice = Suffice(Equal(h[n], 1), Equal(h[n + 1], 1), plausible=True)

    Eq << Eq.suffice.this.lhs.lhs.definition

    Eq << Eq[-1].this.lhs.lhs.apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.rhs.lhs.definition

    Eq << Eq[-1].this.rhs.lhs.apply(algebra.bool.to.piecewise)

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq.equality, Eq.suffice, n=n)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()
