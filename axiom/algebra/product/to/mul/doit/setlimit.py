from util import *


@apply
def apply(self):
    from axiom.algebra.sum.to.add.doit.setlimit import doit
    assert self.is_Product
    return Equal(self, doit(self))


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(oo, k))
    i = Symbol.i(integer=True)

    n = 5
    finiteset = {i for i in range(n)}

    Eq << apply(Product[i:finiteset](x[i]))

    n -= 1
    Eq << Eq[-1].this.lhs.apply(algebra.product.to.mul.dissect, cond={n}, simplify=False)

    Eq << Eq[-1].this.lhs.find(Product).simplify()

    n -= 1
    Eq << Eq[-1].lhs.find(Product).this.apply(algebra.product.to.mul.dissect, cond={n}, simplify=False)

    Eq << Eq[-1].this.rhs.find(Product).simplify()

    n -= 1
    Eq << Eq[-1].rhs.find(Product).this.apply(algebra.product.to.mul.dissect, cond={n})

    Eq << Eq[-1].this.rhs.find(Product).simplify()

    n -= 1
    Eq << Eq[-1].rhs.find(Product).this.apply(algebra.product.to.mul.dissect, cond={n})

    Eq << Eq[5].subs(Eq[-1])

    Eq << Eq[4].subs(Eq[-1])

    Eq << Eq[2].subs(Eq[-1])


if __name__ == '__main__':
    run()

