from util import *


@apply
def apply(imply, c):
    e, interval = imply.of(Contains)
    return Contains(e - c, interval + -c)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(complex=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    Eq << apply(Contains(x, Interval(a, b)), c=c)

    Eq << sets.contains.imply.le.split.interval.apply(Eq[1])

    Eq << sets.contains.imply.ge.split.interval.apply(Eq[1])

    Eq << sets.contains.given.et.split.interval.apply(Eq[0])

    


if __name__ == '__main__':
    run()

