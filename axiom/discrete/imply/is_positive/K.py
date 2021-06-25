from util import *

from axiom.discrete.K.to.add.definition import K


@apply
def apply(x):
    assert x.is_positive
    return Greater(K(x), 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, positive=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True, given=False)

    Eq << apply(x[:n])

    Eq.initial0 = Eq[-1].subs(n, 1)

    Eq << Eq.initial0.this.lhs.defun()

    Eq.initial1 = Eq[-1].subs(n, 2)

    Eq << Eq.initial1.this.lhs.defun()

    Eq.induct = Eq[0].subs(n, n + 2)

    Eq << Eq.induct.this.lhs.defun()

    Eq.hypothesis = Eq[0].subs(n, n + 1)

    Eq << Eq.hypothesis * x[n + 1] + Eq[0]

    Eq << Eq.induct.induct()

    Eq << algebra.cond.cond.suffice.imply.cond.induct.apply(Eq.initial0, Eq.initial1, Eq[-1], n=n, start=1)

    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[0].subs(n, n + 2)


if __name__ == '__main__':
    run()

