from util import *



@apply
def apply(given):
    lhs, rhs = given.of(Less)

    b0, e0 = lhs.of(Pow)
    b1, e1 = rhs.of(Pow)
    assert e0.is_even
    assert e1.is_even

    e0 //= 2
    e1 //= 2

    return Less(abs(b0 ** e0), abs(b1 ** e1))


@prove
def prove(Eq):
    from axiom import algebra
    x, y = Symbol(real=True, given=True)

    Eq << apply(Less(x * x, y * y))

    Eq << ~Eq[1]

    Eq << algebra.ge.imply.ge.square.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]

if __name__ == '__main__':
    run()

