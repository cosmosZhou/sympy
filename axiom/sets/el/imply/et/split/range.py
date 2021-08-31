from util import *


@apply
def apply(given, right_open=True):
    x, (a, b) = given.of(Element[Range])
    if right_open:
        return x >= a, x < b
    else:
        return x >= a, x <= b - 1


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(real=True, given=True)
    a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Range(a, b)), False)



    Eq << sets.el.imply.le.split.range.stop.apply(Eq[0])

    Eq << sets.el.imply.ge.split.range.apply(Eq[0])


if __name__ == '__main__':
    run()

