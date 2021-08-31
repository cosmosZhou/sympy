from util import *

# given: |A| >= 1
# A != {}


@apply
def apply(greater_than, _greater_than):
    a, x = greater_than.of(Greater)
    b, _x = _greater_than.of(LessEqual)
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
    #Eq << apply(x > b, x <= a)
    Eq << apply(b > x, a <= x)

    Eq << sets.el.given.et.split.range.apply(Eq[-1])



    Eq << Eq[-1].reversed

    Eq << Eq[-2].reversed


if __name__ == '__main__':
    run()

