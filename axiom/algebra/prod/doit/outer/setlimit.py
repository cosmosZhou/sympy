from util import *


@apply
def apply(self):
    from axiom.algebra.sum.doit.outer.setlimit import doit
    return Equal(self, doit(Product, self))


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True, shape=(oo, oo))
    i, j, k, a = Symbol(integer=True)
    f, g = Function(etype=dtype.integer)


    Eq << apply(Product[k:g(i), j:f(i), i:{a}](x[i, j]))

    s = Function(eval=lambda i: Product[k:g(i), j:f(i)](x[i, j]))
    Eq << s(i).this.defun()

    Eq << algebra.eq.imply.eq.prod.apply(Eq[-1], (i, {a}))

    Eq << Eq[-1].this.lhs.defun()

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

