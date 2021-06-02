from util import *
from axiom.algebra.cond.cond.imply.cond import process_given_conditions


@apply
def apply(*given, **kwargs):
    eq, f_eq = process_given_conditions(*given, **kwargs)
    return And(eq, f_eq.simplify())


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    h = Function.h(shape=(), integer=True)

    Eq << apply(NotContains(x, S), Equal(Piecewise((f(x), NotContains(x, S)), (g(x), True)), h(x)))

    Eq << algebra.cond.cond.imply.cond.apply(Eq[0], Eq[1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

