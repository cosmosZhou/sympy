from util import *


@apply
def apply(given): 
    (fx, *limits), M = given.of(Equal[Sup])
    return All(M >= fx, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    M, x, a, b = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Equal(M, Sup[x:a:b](f(x))))

    Eq << algebra.eq.imply.ge.apply(Eq[0]).reversed

    Eq << algebra.le_sup.imply.all_le.apply(Eq[-1])
    Eq << Eq[-1].this.expr.reversed


if __name__ == '__main__':
    run()