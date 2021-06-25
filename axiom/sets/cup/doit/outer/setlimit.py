from util import *


@apply
def apply(self):
    from axiom.algebra.sum.doit.outer.setlimit import doit    
    return Equal(self, doit(Cup, self))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(etype=dtype.real, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m = Symbol.m(integer=True, positive=True)

    a = Symbol.a(integer=True)
    f = Function.f(real=True)
    g = Function.g(real=True)
    Eq << apply(Cup[i:g(i, j) > 0, j:f(i, j) > 0, i:{a}](x[i, j]))

    u = Function.u(eval=lambda a: Cup[i:g(i, j) > 0, j:f(a, j) > 0](x[i, j]))

    Eq << u(i).this.defun()

    Eq << sets.eq.imply.eq.cup.apply(Eq[-1], (i, {a}))

    Eq << Eq[-1].this.lhs.defun()

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

