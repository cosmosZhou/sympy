from util import *


@apply(given=None)
def apply(self):
    x, b = self.of(GreaterEqual)
    domain = x.domain
    a, b = domain.of(Range)

    return Equivalent(self, Equal(x, b - 1))


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol(integer=True)
    b = Symbol(integer=True, given=True)
    x = Symbol(domain=Range(a, b + 1), given=True)
    Eq << apply(x >= b)

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.ge.imply.eq.squeeze.range)
    Eq << Eq[-1].this.rhs.apply(algebra.eq.imply.ge)


if __name__ == '__main__':
    run()
# created on 2019-06-04
# updated on 2019-06-04
