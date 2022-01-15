from util import *


@apply(given=None)
def apply(given):
    (x, a), (S[x], b) = given.of(Greater | Greater)
    return Equivalent(given, Greater(x, Min(a, b)))


@prove
def prove(Eq):
    from axiom import algebra
    
    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Greater(x, a) | Greater(x, b))
    
    Eq << algebra.iff.given.et.apply(Eq[0])
    
    Eq << Eq[-1].this.rhs.apply(algebra.gt_min.imply.ou.gt)
    
    Eq << Eq[-2].this.rhs.apply(algebra.gt_min.given.ou.gt)


if __name__ == '__main__':
    run()
# created on 2022-01-02
