from util import *


@apply
def apply(self):
    from axiom.algebra.sum.doit.outer.setlimit import doit
    assert self.is_Product
    return Equal(self, doit(self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    k = Symbol.k(integer=True)
    f = Function.f(etype=dtype.integer)
    g = Function.g(etype=dtype.integer)

    a = Symbol.a(integer=True)

    Eq << apply(Product[k:g(i), j:f(i), i:{a}](x[i, j]))

    s = Function.s(eval=lambda i: Product[k:g(i), j:f(i)](x[i, j]))
    Eq << s(i).this.defun()

    Eq << algebra.eq.imply.eq.product.apply(Eq[-1], (i, {a}))

    Eq << Eq[-1].this.lhs.defun()

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

