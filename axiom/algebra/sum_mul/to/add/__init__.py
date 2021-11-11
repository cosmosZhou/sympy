from util import *


@apply
def apply(self):
    mul, *limits = self.of(Sum)
    from axiom.algebra.mul.to.add import convert
    add = convert(mul)

    from axiom.algebra.sum.to.add import associate
    rhs = associate(Sum, Sum(add, *limits))

    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    i = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    f, h, g = Function(real=True)
    Eq << apply(Sum[i:n]((f(i) + h(i)) * g(i)))

    Eq << Eq[-1].this.lhs.expr.apply(algebra.mul.to.add)
    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)


if __name__ == '__main__':
    run()

from . import st
# created on 2020-03-27
# updated on 2020-03-27
