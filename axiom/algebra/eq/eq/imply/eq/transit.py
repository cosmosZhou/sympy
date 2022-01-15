from util import *


def transit(b_eq_x, x_eq_a, reverse=False):
    b, x = b_eq_x.of(Equal)
    _x, a = x_eq_a.of(Equal)
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
    return Equal(b, a)


@apply
def apply(eq, eq_1, reverse=False):
    return transit(eq, eq_1, reverse=reverse)


@prove
def prove(Eq):
    a, x, b = Symbol(etype=dtype.real)

    Eq << apply(Equal(b, x), Equal(x, a))

    Eq << Eq[1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
# created on 2018-01-09
