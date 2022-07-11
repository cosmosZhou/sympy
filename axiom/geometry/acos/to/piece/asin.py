from util import *


@apply
def apply(self):
    x = self.of(acos)
    #assert x in Interval(-1, 1)
    return Equal(self, Piecewise((ArcSin(sqrt(1 - x ** 2)), x >= 0), (S.Pi - ArcSin(sqrt(1 - x ** 2)), True)))


@prove
def prove(Eq):
    from axiom import geometry, algebra

    x = Symbol(domain=Interval(-1, 1))
    Eq << apply(acos(x))

    Eq << Eq[0].this.lhs.apply(geometry.acos.to.add.asin)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[1], cond=x >= 0)

    Eq <<= algebra.infer.given.infer.subs.bool.apply(Eq[-2]), algebra.infer.given.infer.subs.bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-2].this.rhs.apply(algebra.eq.transport), Eq[-1].this.rhs.apply(algebra.eq.transport)

    Eq.is_nonnegative, Eq.is_negative = Eq[-2].this.rhs.reversed, Eq[-1].this.rhs.apply(algebra.eq.transport, rhs=0)

    Eq << Eq.is_negative.this.rhs.reversed

    Eq << -Eq[-1].this.rhs

    Eq << Eq.is_nonnegative.this.lhs.apply(geometry.ge_zero.imply.eq.add.asin)

    Eq << Eq[-1].this.lhs.apply(geometry.lt_zero.imply.eq.add.asin)

    #https://en.wikipedia.org/wiki/Argument_(complex_analysis)


if __name__ == '__main__':
    run()
# created on 2018-07-14
