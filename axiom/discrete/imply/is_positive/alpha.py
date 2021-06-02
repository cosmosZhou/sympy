from util import *

import axiom


def alpha_step(*args):
    if len(args) == 1:
        x = args[0]
        if x.shape:
            assert len(x.shape) == 1
            n, *_ = x.shape
            assert n > 0
            return Piecewise((x[0], Equal(n, 1)),
                             (x[0] + 1 / alpha(x[1:]), True))
        else:
            return x
    else:
        x, *args = args
        if x.shape:
            assert len(x.shape) == 1
            n, *_ = x.shape
            assert n > 0
            return Piecewise((x[0] + 1 / alpha(*args), Equal(n, 1)),
                             (x[0] + 1 / alpha(x[1:], *args), True))
        else:
            return x + 1 / alpha(*args)


alpha = Function.alpha(eval=alpha_step, shape=())


@apply
def apply(x, n):
    return Greater(alpha(x[:n]), 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, positive=True, shape=(oo,))
    n = Symbol.n(integer=True, positive=True, given=False)

    Eq << apply(x, n)

    Eq.initial = Eq[-1].subs(n, 1)

    Eq << Eq.initial.this.lhs.defun()

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.defun()

    Eq << algebra.cond.imply.cond.subs.apply(Eq[0], x[:n], x[1:n + 1])

    Eq << Eq[-1].apply(algebra.is_positive.imply.is_positive.div)

    Eq << Eq[-1] + x[0]

    Eq << algebra.gt.imply.gt.relaxed.apply(Eq[-1], 0)

    Eq << Eq.induct.induct()

    Eq << algebra.cond.suffice.imply.cond.induct.apply(Eq.initial, Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

