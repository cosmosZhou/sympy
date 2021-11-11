from util import *



@apply(given=None)
def apply(self):
    n = self.of(Equal[Expr % 2, 1])
    return Equivalent(self, Equal((-1) ** n, -1))


@prove
def prove(Eq):
    from axiom import algebra
#     n = q * d + r
    n = Symbol(integer=True)

    Eq << apply(Equal(n % 2, 1))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.is_odd.imply.eq.pow)

    Eq << Eq[-1].this.rhs.apply(algebra.is_odd.given.eq)


if __name__ == '__main__':
    run()
# created on 2019-10-13
# updated on 2019-10-13
