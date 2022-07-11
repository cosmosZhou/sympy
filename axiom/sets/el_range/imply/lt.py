from util import *


@apply
def apply(given):
    assert given.is_Element
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

    x, a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Range(a, b)))

    Eq << sets.el_range.imply.et.apply(Eq[0])




if __name__ == '__main__':
    run()

# created on 2021-03-12
