from util import *



@apply
def apply(imply):
    assert imply.is_Contains

    e, interval = imply.args

    return Contains(-e, -interval)


@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Contains(x, Interval(a, b)))

    Eq << sets.contains.imply.contains.neg.apply(Eq[1])


if __name__ == '__main__':
    run()

