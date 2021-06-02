from util import *

import axiom



@apply
def apply(imply):
    piecewise, sym = imply.of(BinaryCondition)
    if not piecewise.is_Piecewise:
        imply = imply.reversed
        piecewise, sym = imply.args

    piecewise = piecewise.of(Piecewise)

    univeralSet = S.BooleanTrue
    args = []

    for expr, cond in piecewise:
        condition = cond & univeralSet
        if not cond:
            invert = condition.invert()
            univeralSet &= invert

        eq = condition & imply.func(expr, sym).simplify()
        args.append(eq)

    return Or(*args)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    A = Symbol.A(etype=dtype.real * k, given=True)
    B = Symbol.B(etype=dtype.real * k, given=True)

    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    h = Function.h(shape=(), real=True)
    p = Symbol.p(real=True, shape=(), given=True)

    Eq << apply(LessEqual(Piecewise((f(x), Contains(x, A)), (g(x), Contains(x, B)), (h(x), True)), p))

    Eq << algebra.ou.imply.le.apply(Eq[1], wrt=p)


if __name__ == '__main__':
    run()

from . import domain_defined