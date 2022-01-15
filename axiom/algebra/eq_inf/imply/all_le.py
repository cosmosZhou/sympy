from util import *


@apply
def apply(given):
    (fx, *limits), M = given.of(Equal[Inf])
    return All(M <= fx, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(M, Inf[x:a:b](f(x))))

    Eq << algebra.eq.imply.le.apply(Eq[0]).reversed

    Eq << algebra.inf_ge.imply.all_ge.apply(Eq[-1])

    Eq << Eq[-1].this.expr.reversed


if __name__ == '__main__':
    run()
# created on 2019-04-23
