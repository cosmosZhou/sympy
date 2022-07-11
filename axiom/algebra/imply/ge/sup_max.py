from util import *


@apply
def apply(sup):
    fx, *limits = sup.of(Sup)
    return sup >= Maxima(fx, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    M, x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Sup[x:S](f(x)))

    Eq << Eq[0].this.lhs.apply(algebra.sup.to.reducedMin)

    Eq << Eq[-1].this.lhs.apply(algebra.reducedMin.to.minima)

    Eq << algebra.ge_minima.given.all_ge.apply(Eq[-1])

    Eq << algebra.all.given.infer.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.all_le.imply.le.maxima)


if __name__ == '__main__':
    run()
# created on 2019-09-21
