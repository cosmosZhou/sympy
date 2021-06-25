from util import *



@apply
def apply(given):
    is_nonzero_x, is_nonzero_y = given.of(And)
    x = is_nonzero_x.of(Unequal[0])
    y = is_nonzero_y.of(Unequal[0])
    return Unequal(x * y, 0)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    Eq << apply(Unequal(x, 0) & Unequal(y, 0))

    Eq << algebra.is_nonzero.imply.et.apply(Eq[1])

if __name__ == '__main__':
    run()
