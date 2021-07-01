from util import *


@apply
def apply(self):
    assert self.is_Product

    return Equal(self, self.func(self.function ** Bool(self.limits_cond), *((x,) for x, *_ in self.limits)))


@prove
def prove(Eq):
    from axiom import algebra
    S = Symbol.S(etype=dtype.integer)
    x = Symbol.x(integer=True)
    f = Function.f(real=True)

    Eq << apply(Product[x:S](f(x)))

    Eq << Eq[0].this.find(Bool).apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.rhs.function.apply(algebra.pow.to.piecewise.exponent)


if __name__ == '__main__':
    run()

