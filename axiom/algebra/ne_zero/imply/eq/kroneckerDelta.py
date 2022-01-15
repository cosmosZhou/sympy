from util import *


@apply
def apply(given):
    assert given.is_Unequal
    assert given.rhs.is_zero
    assert given.lhs.is_KroneckerDelta
    return Equal(*given.lhs.args)


@prove
def prove(Eq):
    a, b = Symbol(real=True)
    Eq << apply(Unequal(KroneckerDelta(a, b), 0))

    Eq << Eq[0].simplify()


if __name__ == '__main__':
    run()
# created on 2020-09-05
