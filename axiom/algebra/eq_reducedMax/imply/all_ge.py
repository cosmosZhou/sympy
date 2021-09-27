from util import *


@apply
def apply(given):
    arg, M = given.of(Equal[ReducedMax])
    fx, *limits = arg.of(Cup[FiniteSet])
    return All(M >= fx, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    M, x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Equal(M, ReducedMax({f(x): Element(x, S)})))

    Eq << Eq[0].this.rhs.apply(algebra.reducedMax.to.maxima)

    Eq << algebra.eq_maxima.imply.all_ge.apply(Eq[-1])


if __name__ == '__main__':
    run()