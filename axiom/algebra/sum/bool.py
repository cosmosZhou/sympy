from util import *


@apply
def apply(self):
    assert self.is_Sum

    return Equal(self, self.func(self.function * Bool(self.limits_cond), *((x,) for x, *_ in self.limits)))


@prove
def prove(Eq):
    from axiom import algebra
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(real=True)

    Eq << apply(Sum[x:A, y:B](f(x, y)))

    Eq << Eq[0].this.rhs.function.args[1].apply(algebra.bool.to.mul)

    Eq << Sum[x](Eq[-1].rhs.function).this.function.args[1].apply(algebra.bool.to.piecewise)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.mul)

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (y,))

    Eq << Eq[1].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.function.args[0].apply(algebra.bool.to.piecewise)


if __name__ == '__main__':
    run()

