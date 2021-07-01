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
    k = Symbol.k(integer=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    f = Function.f(integer=True)
    Eq << apply(Mul(Product[k:A // B](f(k)), Product[k:A & B](f(k))))

    Eq << Eq[0].this.find(Product).apply(algebra.product.bool)

    Eq << Eq[-1].this.lhs.find(Product).apply(algebra.product.bool)

    Eq << Eq[-1].this.lhs.find(Product).apply(algebra.product.bool)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.product)

    Eq << Eq[-1].this.lhs.function.apply(algebra.mul.to.pow.add.exponent)

    Eq << Eq[-1].this.find(Add).apply(algebra.add.inclusive_exclusive_principle)


if __name__ == '__main__':
    run()
