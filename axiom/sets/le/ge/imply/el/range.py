from util import *


@apply
def apply(le, ge):
    x, a = le.of(LessEqual)
    _x, b = ge.of(GreaterEqual)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
    assert x == _x
    assert x.is_integer
    return Element(x, Range(b, a + 1))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, x = Symbol(integer=True, given=True)
    #Eq << apply(x >= b, a >= x)
    Eq << apply(x <= b, x >= a)

    Eq << sets.el.given.et.split.range.apply(Eq[-1])



    Eq << algebra.lt.given.le.apply(Eq[-1])


if __name__ == '__main__':
    run()

