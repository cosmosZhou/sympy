from util import *


@apply(given=None)
def apply(all_le):
    (lhs, rhs), *limits = all_le.of(All[GreaterEqual])
    lhs = Lamda(lhs, *limits).simplify()
    rhs = Lamda(rhs, *limits).simplify()
    return Equivalent(all_le, lhs >= rhs)


@prove
def prove(Eq):
    from axiom import algebra
    
    n = Symbol(integer=True, positive=True)
    x, y = Symbol(shape=(n,), real=True)
    i = Symbol(integer=True)
    Eq << apply(All[i:n](x[i] >= y[i]))
    
    Eq << algebra.iff.given.et.apply(Eq[0])
    
    Eq << Eq[-2].this.lhs.apply(algebra.all_ge.imply.ge.lamda)
    
    Eq << Eq[-1].this.lhs.apply(algebra.all_ge.given.ge.lamda)


if __name__ == '__main__':
    run()
# created on 2022-03-31
