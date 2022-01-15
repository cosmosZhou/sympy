from util import *


@apply(given=None)
def apply(ge):
    x, a = ge.of(Abs >= Expr)
    return Equivalent(ge, Or(x <= -a, x >= a))


@prove
def prove(Eq):
    from axiom import algebra
    
    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) >= a)
    
    Eq << algebra.iff.given.et.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.apply(algebra.abs_ge.imply.ou)
    
    Eq << Eq[-1].this.lhs.apply(algebra.abs_ge.given.ou)


if __name__ == '__main__':
    run()
# created on 2022-01-07
