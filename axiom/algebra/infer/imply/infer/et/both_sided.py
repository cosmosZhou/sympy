from util import *


@apply(simplify=False)
def apply(given, *, cond=None):
    lhs, rhs = given.of(Infer)
    cond = sympify(cond)
    return Infer(cond & lhs, cond & rhs)


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, nonnegative=True, given=True)
    f, g = Symbol(integer=True, shape=(oo,), given=True)
    a, b = Symbol(integer=True)
    Eq << apply(Infer(LessEqual(f[0], g[0]), LessEqual(f[n], g[n])), cond=LessEqual(a, b))

    Eq << Infer(LessEqual(a, b), LessEqual(a, b), plausible=True)

    Eq << algebra.infer.infer.imply.infer.et.apply(Eq[-1], Eq[0], simplify=None)


if __name__ == '__main__':
    run()
# created on 2018-03-31
