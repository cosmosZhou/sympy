from util import *


@apply
def apply(given, t):
    e, interval = given.of(Contains)
    t = sympify(t)
    return Contains(e + -t, interval + -t)


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    t = Symbol.t(real=True)
    Eq << apply(Contains(x, Interval(a, b)), t)

    Eq << sets.contains.imply.contains.add.apply(Eq[0], -t)


if __name__ == '__main__':
    run()

