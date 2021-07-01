from util import *



@apply
def apply(*given, n=None, x=None, start=0, return_hypothesis=True):
    start = sympify(start)
    f0, suffice = given
    f0.of(Equal)
    fn, fn1 = suffice.of(Suffice)

    x_wild = Wild('x', **x.type.dict)
    fn_hypothesis = fn
    fn = fn._subs(x, x_wild)

    x_, *_ = fn1._subs(n, n - 1).match(fn).values()

    x0_, *_ = f0.match(fn._subs(n, start)).values()

    assert n.domain.min() == start

    fn = fn._subs(x_wild, x_)
    if return_hypothesis:
        return fn, fn_hypothesis
    return fn


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True)
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)

    Eq << apply(Equal(f[0](z), g[0](z)), Suffice(Equal(f[n](x), g[n](x)), Equal(f[n + 1](y), g[n + 1](y))), n=n, x=x)

    Eq << Eq[0].subs(z, y)

    Eq << Eq[1].subs(x, y)

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq[-2], Eq[-1], n=n)

    Eq << Eq[2].subs(y, x)


if __name__ == '__main__':
    run()
