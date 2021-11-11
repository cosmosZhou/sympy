from util import *


@apply
def apply(self):
    assert self.is_Product

    return Equal(self, self.func(self.expr ** Bool(self.limits_cond), *((x,) for x, *_ in self.limits)))


@prove
def prove(Eq):
    from axiom import algebra
    S = Symbol(etype=dtype.integer)
    x = Symbol(integer=True)
    f = Function(real=True)

    Eq << apply(Product[x:S](f(x)))

    Eq << Eq[0].this.find(Bool).apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.rhs.expr.apply(algebra.pow.to.piece.exponent)


if __name__ == '__main__':
    run()

# created on 2018-04-13
# updated on 2018-04-13
