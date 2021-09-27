from util import *


@apply
def apply(given):
    arg, M = given.of(Equal[ReducedMin])
    fx, *limits = arg.of(Cup[FiniteSet])
    return All(M <= fx, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    M, x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Equal(M, ReducedMin({f(x): Element(x, S)})))

    Eq << Eq[0].this.rhs.apply(algebra.reducedMin.to.minima)
    Eq << algebra.eq_minima.imply.all_le.apply(Eq[-1])


if __name__ == '__main__':
    run()