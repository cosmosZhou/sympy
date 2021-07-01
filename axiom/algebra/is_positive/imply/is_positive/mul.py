from util import *


@apply
def apply(given, factor):
    assert factor > 0
    x = given.of(Expr > 0)

    return Greater(x * factor, 0)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True)
    k = Symbol.k(integer=True)
    h = Symbol.h(real=True, shape=(n,))
    a = Symbol.a(real=True, positive=True)
    Eq << apply(h[k] > 0, a)

    Eq << Greater(a, 0, plausible=True)

    Eq << algebra.is_positive.is_positive.imply.is_positive.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()