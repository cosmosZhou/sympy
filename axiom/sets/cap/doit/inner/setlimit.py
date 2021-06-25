from util import *


@apply
def apply(self):
    from axiom.algebra.all.doit.inner.setlimit import doit
    return Equal(self, doit(Cap, self))


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(etype=dtype.real, shape=(oo, oo))
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    m = Symbol.m(integer=True, positive=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    c = Symbol.c(integer=True)
    d = Symbol.d(integer=True)

    Eq << apply(Cap[j:{a, b, c, d}, i:m](x[i, j]))

    s = Function.s(eval=lambda i: Cap[j:{a, b, c, d}](x[i, j]), etype=dtype.real)
    Eq << s(i).this.defun()

    Eq << sets.eq.imply.eq.cap.apply(Eq[-1], (i, 0, m))

    Eq << Eq[-2].this.rhs.apply(sets.cap.to.intersection.doit.setlimit)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

