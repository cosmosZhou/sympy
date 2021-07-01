from util import *



@apply
def apply(*given):
    unequality, equality = given
    if not unequality.is_Unequal:
        unequality, equality = equality, unequality
    assert unequality.is_Unequal
    unequality.rhs.is_zero

    divisor = unequality.lhs
    return Equal(equality.lhs / divisor, equality.rhs / divisor)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Unequal(x, 0), Equal(x * a, b))

    Eq << Eq[1] / x
    Eq <<= Eq[-1] & Eq[0]

    Eq << algebra.et.imply.et.apply(Eq[-1])


if __name__ == '__main__':
    run()
