from util import *


@apply
def apply(cond, necessary):
    lhs, rhs = necessary.of(Necessary)
    assert cond == rhs

    return lhs


@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, nonnegative=True, given=True)
    f, g = Symbol(integer=True, shape=(oo,), given=True)
    Eq << apply(LessEqual(f[0], g[0]), Necessary(LessEqual(f[n], g[n]), LessEqual(f[0], g[0])))

    Eq << algebra.cond.suffice.imply.cond.transit.apply(Eq[0], Eq[1].reversed)

    

    

    


if __name__ == '__main__':
    run()