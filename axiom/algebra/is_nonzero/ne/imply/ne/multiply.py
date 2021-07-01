from util import *



@apply
def apply(*given):
    unequality, eq = given
    assert eq.is_Unequal
    assert unequality.is_Unequal
    unequality.rhs.is_zero

    factor = unequality.lhs
    return Unequal(eq.lhs * factor, eq.rhs * factor)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(real=True, given=True)
    a = Symbol.a(real=True, given=True)
    b = Symbol.b(real=True, given=True)
    Eq << apply(Unequal(x, 0), Unequal(a, b))

    Eq << ~Eq[-1]

    Eq << algebra.is_nonzero.eq.imply.eq.div.apply(Eq[0], Eq[-1])

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()
