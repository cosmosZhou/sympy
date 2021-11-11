from util import *


@apply
def apply(ne, contains):
    if ne.is_Element:
        ne, contains = contains, ne
    _x, y = ne.of(Unequal)
    x, s = contains.of(Element)

    if x != _x:
        _x, y = y, _x
    assert x == _x

    return Element(x, s - y.set)


@prove
def prove(Eq):
    from axiom import sets

    x, y = Symbol(integer=True, given=True)
    s = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Unequal(x, y), Element(x, s))

    Eq << sets.ne.imply.notin.apply(Eq[0], simplify=False)

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

# created on 2018-05-11
# updated on 2018-05-11
