from util import *


@apply
def apply(self):
    from axiom.algebra.sum.limits.domain_defined.insert import limits_insert
    assert self.is_Product
    return Equal(self, limits_insert(self))


@prove
def prove(Eq):
    from axiom import algebra
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(shape=(k,), integer=True)

    f = Function.f(etype=dtype.integer)
    h = Function.h(real=True)

    Eq << apply(Product[j:f(i), i](h(x[i], j)))

    Eq << Eq[-1].this.rhs.apply(algebra.product.limits.domain_defined.delete)


if __name__ == '__main__':
    run()

