from util import *



@apply
def apply(*given):
    cond, suffice = given

    lhs, rhs = suffice.of(Suffice)
    assert cond == lhs

    return rhs


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, nonnegative=True, given=True)
    f = Symbol.f(integer=True, shape=(oo,), given=True)
    g = Symbol.g(integer=True, shape=(oo,), given=True)

    Eq << apply(LessEqual(f[0], g[0]), Suffice(LessEqual(f[0], g[0]), LessEqual(f[n], g[n])))

    Eq << Eq[1].apply(algebra.suffice.imply.ou)

    Eq <<= Eq[-1] & Eq[0]

    Eq << ~Eq[2]

    Eq <<= Eq[-1] & Eq[-2]


if __name__ == '__main__':
    run()
