from util import *

# given: |A| >= 1
# A != {}


@apply
def apply(lt, ge):
    x, a = lt.of(Less)
    _x, b = ge.of(GreaterEqual)
    if x != _x:
        a, x, _x, b = _x, b, a, x,
        a += 1
        b += 1

    assert x == _x

    assert x.is_integer
    return Element(x, Range(b, a))


@prove
def prove(Eq):
    from axiom import sets

    a, b, x = Symbol(integer=True, given=True)
    #Eq << apply(b < x, a >= x)
    Eq << apply(x < b, x >= a)

    Eq << sets.el_range.given.et.apply(Eq[-1])



    #Eq << Eq[-1].reversed
    #Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

# created on 2020-03-20
