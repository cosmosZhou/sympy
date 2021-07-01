from util import *


@apply
def apply(given):
    assert given.is_Contains
    x, interval = given.args
    a, b = interval.of(Range)

    if interval.right_open:
        return Less(x, b)
    else:
        if interval.left_open:
            return Less(a, x)
        else:
            ...


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(integer=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Contains(x, Range(a, b)))

    Eq << sets.contains.imply.et.split.range.apply(Eq[0])

    


if __name__ == '__main__':
    run()

