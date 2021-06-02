from util import *


@apply
def apply(given):
    from axiom.algebra.all.imply.all.limits.merge import merge
    return merge(given)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    x = Symbol.x(real=True, shape=(oo,))
    f = Function.f(real=True)

    Eq << apply(ForAll[x[:n]:CartesianSpace(Interval(a, b), n), x[n]:Interval(a, b)](f(x[:n + 1]) > 0))

    Eq << algebra.all.imply.all.limits.split.apply(Eq[1], index=n)


if __name__ == '__main__':
    run()

