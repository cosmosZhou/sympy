from util import *


@apply
def apply(given, right_open=True):
    x, (a, b) = given.of(Contains[Range])
    if right_open:
        return x >= a, x < b
    else:
        return x >= a, x <= b - 1


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(real=True, given=True)
    a = Symbol.a(integer=True, given=True)
    b = Symbol.b(integer=True, given=True)
    Eq << apply(Contains(x, Range(a, b)), False)

    

    Eq << sets.contains.imply.le.split.range.stop.apply(Eq[0])

    Eq << sets.contains.imply.ge.split.range.apply(Eq[0])


if __name__ == '__main__':
    run()

