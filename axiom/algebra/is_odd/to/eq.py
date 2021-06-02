from util import *



@apply(given=None)
def apply(self):
    n = self.of(Equal[Basic % 2, 1])
    return Equivalent(self, Equal((-1) ** n, -1))


@prove
def prove(Eq):
    from axiom import algebra
#     n = q * d + r
    n = Symbol.n(integer=True)

    Eq << apply(Equal(n % 2, 1))

    Eq << algebra.equivalent.given.suffice.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.is_odd.imply.eq.pow)

    Eq << Eq[-1].this.rhs.apply(algebra.is_odd.given.eq)


if __name__ == '__main__':
    run()
