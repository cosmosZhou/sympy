from util import *


@apply
def apply(x):
    from axiom.discrete.imply.is_positive.alpha import alpha
    return Unequal(alpha(x), 0)


@prove
def prove(Eq):
    from axiom import discrete, algebra
    x = Symbol(integer=True, shape=(oo,))
    n = Symbol(integer=True, positive=True)

    Eq << apply(x[:n])

    Eq << discrete.imply.is_positive.alpha.apply(x, n)

    Eq << Eq[-1].apply(algebra.is_positive.imply.is_nonzero)


if __name__ == '__main__':
    run()

