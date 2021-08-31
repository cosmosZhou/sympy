from util import *


@apply
def apply(given, index):
    eqs, *limits = given.of(Any[And])
    eq = eqs[index]
    return Any(eq, *limits)


@prove
def prove(Eq):
    from axiom import algebra

    x, c = Symbol(real=True)
    a, b = Symbol(real=True, given=True)
    f = Function(shape=(), real=True)
    Eq << apply(Any[x:a:b]((x <= c) & (f(x) >= 1)), index=0)

    Eq << ~Eq[-1]

    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

