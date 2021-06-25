from util import *



@apply
def apply(*given, n=None, x=None, start=0):
    start = sympify(start)
    f0, suffice = given
    f0.of(Equal)
    fn_and_fnt, fn1 = suffice.of(Suffice)

    fn, fnt = fn_and_fnt.of(And)

    if fn1._subs(n, n - 1) == fnt:
        fn, fnt = fnt, fn

    assert fn1._subs(n, n - 1) == fn

    assert fn._subs(x, x + 1) == fnt
    assert fn._subs(n, start) == f0

    assert n.domain.min() == start

    return fn & fnt


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    x = Symbol.x(real=True)

    Eq << apply(Equal(f[0](x), g[0](x)), Suffice(Equal(f[n](x), g[n](x)) & Equal(f[n](x + 1), g[n](x + 1)), Equal(f[n + 1](x), g[n + 1](x))), n=n, x=x)

    fn = Eq[2].args[1]
    Eq << Suffice(fn, fn._subs(x, x + 1), plausible=True)

    Eq << Eq[-1].this.lhs.apply(algebra.eq.imply.eq.subs, x, x + 1)

    Eq << algebra.suffice.imply.suffice.et.apply(Eq[-1])

    Eq << algebra.suffice.suffice.imply.suffice.transit.apply(Eq[-1], Eq[1])

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq[0], Eq[-1], n=n)

    Eq << Eq[-1].subs(x, x + 1)

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()
