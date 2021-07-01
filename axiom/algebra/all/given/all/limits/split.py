from util import *


@apply
def apply(given, index=-1):
    from axiom.algebra.all.imply.all.limits.split import split
    return split(given, index)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    x = Symbol.x(real=True, shape=(oo,))
    f = Function.f(real=True)

    Eq << apply(All[x[:n + 1]:CartesianSpace(Interval(a, b), n + 1)](f(x[:n + 1]) > 0), index=n)

    Eq << algebra.all.imply.all.limits.merge.apply(Eq[1])


if __name__ == '__main__':
    run()

