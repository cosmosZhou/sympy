from util import *


@apply(given=None)
def apply(given):
    (x, a), (S[x], b) = given.of(Less | Less)
    return Equivalent(given, Less(x, Max(a, b)))


@prove
def prove(Eq):
    from axiom import algebra
    
    x, a, b = Symbol(real=True, given=True)
    Eq << apply(Less(x, a) | Less(x, b))
    
    Eq << algebra.iff.given.et.apply(Eq[0])
    
    Eq << Eq[-1].this.rhs.apply(algebra.lt_max.imply.ou.lt)
    
    Eq << Eq[-2].this.rhs.apply(algebra.lt_max.given.ou.lt)


if __name__ == '__main__':
    run()
# created on 2022-01-02
