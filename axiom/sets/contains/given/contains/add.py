from util import *



@apply
def apply(imply, c):
    assert imply.is_Contains

    e, interval = imply.args

    return Contains(e + c, interval + c)


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(complex=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    Eq << apply(Contains(x, Interval(a, b)), c=c)

    Eq << sets.contains.imply.le.split.interval.apply(Eq[1])

    Eq << sets.contains.imply.ge.split.interval.apply(Eq[1])

    Eq << sets.contains.given.et.split.interval.apply(Eq[0])

    Eq << algebra.et.given.conds.apply(Eq[-1])



if __name__ == '__main__':
    run()

