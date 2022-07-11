from util import *


@apply
def apply(greater_than, _greater_than):
    x, a = greater_than.of(Less)
    _x, b = _greater_than.of(Greater)
    if x != _x:
        a, x, _x, b = _x, b, a, x,

    assert x == _x
    assert x.is_integer
    return Element(x, Range(b + 1, a))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(integer=True, given=True)
    #Eq << apply(b < x, a >= x)
    Eq << apply(x < b, x > a)

    Eq << sets.el_range.given.et.apply(Eq[-1])



    Eq << algebra.ge.given.gt.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-05-29
