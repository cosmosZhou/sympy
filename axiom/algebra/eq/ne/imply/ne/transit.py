from util import *


@apply
def apply(eq, not_eq):
    if not eq.is_Equal:
        eq, not_eq = not_eq, eq

    a, x = eq.of(Equal)
    _x, b = not_eq.of(Unequal)
    if x != _x:
        if _x == a:
            a, x = x, a

    assert x == _x
    return Unequal(a, b)


@prove
def prove(Eq):
    x, y, a = Symbol(etype=dtype.integer)
    Eq << apply(Equal(x, y), Unequal(y, a))

    Eq << Eq[1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
# created on 2020-02-11
