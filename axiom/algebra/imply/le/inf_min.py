from util import *


@apply
def apply(self):
    fx, *limits = self.of(Inf)
    return self <= Minima(fx, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    M, x = Symbol(real=True)
    S = Symbol(etype=dtype.real)
    f = Function(real=True)
    Eq << apply(Inf[x:S](f(x)))

    Eq << Eq[0].this.lhs.apply(algebra.inf.to.reducedMax)

    Eq << Eq[-1].this.lhs.apply(algebra.reducedMax.to.maxima)

    Eq << algebra.le_maxima.given.all_le.apply(Eq[-1])

    Eq << algebra.all.given.infer.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.all_ge.imply.ge_minima)


if __name__ == '__main__':
    run()
# created on 2019-01-03
