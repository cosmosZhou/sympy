from util import *


@apply
def apply(is_nonzero_x, is_nonzero_y):
    x = is_nonzero_x.of(Unequal[0])
    y = is_nonzero_y.of(Unequal[0])
    return Unequal(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True, given=True)
    Eq << apply(Unequal(x, 0), Unequal(y, 0))

    Eq << algebra.ne_zero.imply.et.apply(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2018-01-22
