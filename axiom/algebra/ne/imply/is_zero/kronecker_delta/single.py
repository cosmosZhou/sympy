from util import *
import axiom



@apply
def apply(given):
    lhs, rhs = given.of(Unequal)
    return Equal(KroneckerDelta(lhs, rhs), 0)


@prove
def prove(Eq):
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Unequal(x, y))
    
    Eq << Eq[1].this.lhs.astype(Piecewise)    


if __name__ == '__main__':
    run()