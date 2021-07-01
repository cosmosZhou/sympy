from util import *



@apply
def apply(*given):
    equality_A, equality_B = given
    x, a = equality_A.of(Equal)
    _x, b = equality_B.of(Equal)
    assert x == _x

    return Contains(x, a.set & b.set)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)

    Eq << apply(Equal(x, a), Equal(x, b))

    Eq << Eq[-1].subs(Eq[1])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[0], Eq[1])

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()

