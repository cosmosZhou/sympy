from util import *


@apply
def apply(self):
    (function, *limits), variable, count = self.of(Difference[Sum])

    assert count == 1
    rhs = Sum(Difference(function, variable, count).simplify(), *limits)

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    x = Symbol(real=True)
    Eq << apply(Difference(Sum[i:n](f[i](x)), x))

    Eq << Eq[0].this.lhs.doit()

    Eq << Eq[-1].this.rhs.expr.doit()
    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)


if __name__ == '__main__':
    run()
