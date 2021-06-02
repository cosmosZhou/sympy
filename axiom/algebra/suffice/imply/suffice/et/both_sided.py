from util import *
import axiom



@apply(simplify=False)
def apply(given, *, cond=None):
    lhs, rhs = given.of(Suffice)
    return Suffice(cond & lhs, cond & rhs)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True, given=True)
    f = Symbol.f(integer=True, shape=(oo,), given=True)
    g = Symbol.g(integer=True, shape=(oo,), given=True)

    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)

    Eq << apply(Suffice(LessEqual(f[0], g[0]), LessEqual(f[n], g[n])), cond=LessEqual(a, b))

    Eq << Suffice(LessEqual(a, b), LessEqual(a, b), plausible=True)

    Eq << algebra.suffice.suffice.imply.suffice.et.apply(Eq[-1], Eq[0], simplify=None)


if __name__ == '__main__':
    run()
