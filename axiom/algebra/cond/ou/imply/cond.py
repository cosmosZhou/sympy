from util import *
import axiom



@apply
def apply(*given):
    cond, ou = given
    cond = cond.invert()
    for i, c in enumerate(ou.of(Or)):
        if c == cond:
            conds = [*ou.args]
            del conds[i]
            return Or(*conds)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol.x(integer=True)
    S = Symbol.S(etype=dtype.integer)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)

    Eq << apply(Contains(x, S), NotContains(x, S) | (f(x) > g(x)))

    Eq <<= Eq[0] & Eq[1]

    Eq << algebra.et.imply.conds.apply(Eq[-1])

if __name__ == '__main__':
    run()

