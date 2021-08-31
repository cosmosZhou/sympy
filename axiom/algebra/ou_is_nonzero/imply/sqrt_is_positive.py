from util import *


@apply
def apply(ou):
    x, y = ou.of(Unequal[0] | Unequal[0])
    r = sqrt(x ** 2 + y ** 2)
    return Greater(r, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True)
    Eq << apply(Unequal(x, 0) | Unequal(y, 0))

    Eq << algebra.ou_is_nonzero.imply.add_is_positive.square.apply(Eq[0])
    Eq << algebra.is_positive.imply.sqrt_is_positive.apply(Eq[-1])


if __name__ == '__main__':
    run()