from util import *



@apply
def apply(unequality, equality):
    if not unequality.is_Unequal:
        unequality, equality = equality, unequality
    assert unequality.is_Unequal
    unequality.rhs.is_zero

    divisor = unequality.lhs
    return Equal(equality.lhs / divisor, equality.rhs / divisor)


@prove
def prove(Eq):
    from axiom import algebra
    x, a, b = Symbol(real=True)
    Eq << apply(Unequal(x, 0), Equal(x * a, b))

    Eq << Eq[1] / x
    Eq <<= Eq[-1] & Eq[0]

    Eq << algebra.et.imply.et.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-08-13
