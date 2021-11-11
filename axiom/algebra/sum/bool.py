from util import *


@apply
def apply(self):
    function, *limits = self.of(Sum)
    return Equal(self, Sum(function * Bool(self.limits_cond), *((x,) for x, *_ in limits)))


@prove
def prove(Eq):
    from axiom import algebra

    A, B = Symbol(etype=dtype.integer)
    x, y = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[x:A, y:B](f(x, y)))

    Eq << Eq[0].this.rhs.expr.args[1].apply(algebra.bool.to.mul)

    Eq << Sum[x](Eq[-1].rhs.expr).this.expr.args[1].apply(algebra.bool.to.piece)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.mul)

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (y,))

    Eq << Eq[1].this.rhs.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.expr.args[0].apply(algebra.bool.to.piece)


if __name__ == '__main__':
    run()

# created on 2018-02-19
# updated on 2018-02-19
