from util import *


@apply
def apply(self):
    from axiom.algebra.sum.limits.domain_defined.insert import limits_insert
    assert self.is_Product
    return Equal(self, limits_insert(self))


@prove
def prove(Eq):
    from axiom import algebra
    i, j = Symbol(integer=True)
    k = Symbol(integer=True, positive=True)
    x = Symbol(shape=(k,), integer=True)

    f = Function(etype=dtype.integer)
    h = Function(real=True)

    Eq << apply(Product[j:f(i), i](h(x[i], j)))

    Eq << Eq[-1].this.rhs.apply(algebra.prod.limits.domain_defined.delete)


if __name__ == '__main__':
    run()

