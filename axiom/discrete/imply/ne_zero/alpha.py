from util import *


@apply
def apply(x):
    from axiom.discrete.imply.gt_zero.alpha import alpha
    return Unequal(alpha(x), 0)


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol(integer=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)

    Eq << apply(x[:n])

    Eq << discrete.imply.gt_zero.alpha.apply(x, n)

    Eq << Eq[-1].apply(algebra.gt_zero.imply.ne_zero)


if __name__ == '__main__':
    run()

# created on 2020-09-18
