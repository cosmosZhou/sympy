from util import *


@apply
def apply(self):
    from axiom.algebra.add.to.sum.limits.complement import limits_complement
    (function, *limits_a), (_function, *limits_b) = self.of(Product / Product)
    assert function == _function

    limits = limits_complement(limits_a, limits_b, function=function)
    return Equal(self, Product(function, *limits), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    f = Function.f(integer=True)
    Eq << apply(Product[k:A](f(k)) / Product[k:A & B](f(k)))

    Eq << Eq[0].this.lhs.find(Product).apply(algebra.product.to.mul.split, cond=B)


if __name__ == '__main__':
    run()
