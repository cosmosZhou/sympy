from util import *


@apply
def apply(self):
    assert self.is_Bool
    et = self.of(Bool)
    eqs = et.of(And)

    return Equal(self, Mul(*(Bool(eq)for eq in eqs)))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Bool((x > y) & (a > b)))

    Eq << Eq[0].this.rhs.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.rhs.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.rhs.apply(algebra.mul_piecewise.to.piecewise)

    Eq << Eq[-1].this.rhs.apply(algebra.piecewise.flatten, index=0)

    Eq << Eq[-1].this.lhs.apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()

