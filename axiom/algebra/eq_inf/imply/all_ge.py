from util import *


@apply
def apply(given): 
    (fx, *limits), M = given.of(Equal[Inf])
    return All(fx >= M, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(M, Inf[x:a:b](f(x))))

    Eq << algebra.eq_inf.imply.all_le.apply(Eq[0])
    Eq << Eq[-1].this.expr.reversed


if __name__ == '__main__':
    run()