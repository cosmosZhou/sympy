from util import *


@apply
def apply(self):
    from axiom.algebra.sum.doit.outer.setlimit import doit
    return Equal(self, doit(Cap, self))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol(etype=dtype.real, shape=(oo, oo))
    i, j, t, a = Symbol(integer=True)
    m = Symbol(integer=True, positive=True)

    f, g = Function(real=True)
    s = Function(etype=dtype.real)
    Eq << apply(Cap[t:i, i:g(i, j) > 0:s(i), j:f(i, j) > 0, i:{a}](x[i, j]))

    u = Function(eval=lambda a: Cap[t:i, i:g(i, j) > 0:s(a), j:f(a, j) > 0](x[i, j]))

    Eq << u(i).this.defun()

    Eq << sets.eq.imply.eq.cap.apply(Eq[-1], (i, {a}))

    Eq << Eq[-1].this.lhs.defun()

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-01-21
