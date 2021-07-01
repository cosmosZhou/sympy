from util import *


@apply
def apply(given):
    lhs, *limits = given.of(All[Expr >= 0])

    return GreaterEqual(Sum(lhs, *limits), 0)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol.n(integer=True, positive=True)
    i = Symbol.i(integer=True)
    f = Function.f(shape=(), complex=True)
    Eq << apply(All[i:n](f(i) >= 0))

    Eq << algebra.all_ge.imply.ge.sum.apply(Eq[0])


if __name__ == '__main__':
    run()