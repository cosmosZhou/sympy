from util import *



def transit(b_eq_x, x_eq_a, reverse=False):
    b, x = b_eq_x.of(Equivalent)
    _x, a = x_eq_a.of(Equivalent)
    if x != _x:
        if _x == b:
            b, x = x, b
        elif a == b:
            b, x, _x, a = x, b, a, _x
        elif x == a:
            _x, a = a, _x
    assert x == _x
    if reverse:
        b, a = a, b
    return Equivalent(b, a)


@apply
def apply(equivalent_0, equivalent_1, reverse=False):
    return transit(equivalent_0, equivalent_1, reverse=reverse)


@prove
def prove(Eq):
    from axiom import algebra
    a, x, b = Symbol(etype=dtype.real)
    f = Function(real=True)

    Eq << apply(Equivalent(f(b) > 0, f(x) > 0), Equivalent(f(x) > 0, f(a) > 0))

    Eq << algebra.equivalent.given.et.apply(Eq[-1])

    Eq << algebra.equivalent.imply.suffice.apply(Eq[0])

    Eq << algebra.equivalent.imply.suffice.apply(Eq[1])

    Eq << algebra.suffice.suffice.imply.suffice.transit.apply(Eq[-2], Eq[-1])

    Eq << algebra.equivalent.imply.necessary.apply(Eq[0])

    Eq << algebra.equivalent.imply.necessary.apply(Eq[1])

    Eq << algebra.necessary.necessary.imply.necessary.transit.apply(Eq[-2], Eq[-1])

if __name__ == '__main__':
    run()
