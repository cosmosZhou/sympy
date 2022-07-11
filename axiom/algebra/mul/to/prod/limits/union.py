from util import *


@apply
def apply(self):
    from axiom.algebra.add.to.sum.limits.union import limits_union
    (function, *limits_a), (_function, *limits_b) = self.of(Product * Product)
    assert function == _function

    limits = limits_union(limits_a, limits_b, function=function)
    return Equal(self, Product(function, *limits), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    f = Function(integer=True)
    Eq << apply(Mul(Product[k:A - B](f(k)), Product[k:A & B](f(k))))

    Eq << Eq[0].this.find(Product).apply(algebra.prod.bool)

    Eq << Eq[-1].this.lhs.find(Product).apply(algebra.prod.bool)

    Eq << Eq[-1].this.lhs.find(Product).apply(algebra.prod.bool)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.prod)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.mul.to.pow.add.exponent)

    Eq << Eq[-1].this.find(Add).apply(algebra.add.principle.inclusive_exclusive)


if __name__ == '__main__':
    run()
# created on 2020-02-02
