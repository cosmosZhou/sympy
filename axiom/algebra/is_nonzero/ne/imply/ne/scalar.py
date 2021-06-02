from util import *



@apply
def apply(*given):
    unequality, eq = given
    assert eq.is_Unequal
    assert unequality.is_Unequal
    unequality.rhs.is_zero

    divisor = unequality.lhs
    return Unequal(eq.lhs / divisor, eq.rhs / divisor)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Unequal(x, 0), Unequal(x * a, b))

    Eq << algebra.ne.imply.ou.divide.apply(Eq[1], x)

    Eq <<= Eq[-1] & Eq[0]

    Eq << algebra.et.imply.conds.apply(Eq[-1])


if __name__ == '__main__':
    run()
