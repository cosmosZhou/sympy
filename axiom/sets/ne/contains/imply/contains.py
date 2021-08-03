from util import *


@apply
def apply(ne, contains):
    if ne.is_Contains:
        ne, contains = contains, ne
    _x, y = ne.of(Unequal)
    x, s = contains.of(Contains)

    if x != _x:
        _x, y = y, _x
    assert x == _x

    return Contains(x, s - y.set)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    s = Symbol.s(etype=dtype.integer, given=True)
    Eq << apply(Unequal(x, y), Contains(x, s))

    Eq << sets.ne.imply.notcontains.apply(Eq[0], simplify=False)

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

