from util import *


@apply
def apply(given, index=0):

    return given.of(And)[index]


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)

    f = Function.f(real=True)
    g = Function.g(real=True)
    b = Symbol.b(shape=(k,), real=True)

    Eq << apply(And(Unequal(x, y), Unequal(f(x), g(y)), Equal(f(x), b)))

    Eq << Suffice(Eq[0], Eq[1], plausible=True)

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[-1])

if __name__ == '__main__':
    run()

