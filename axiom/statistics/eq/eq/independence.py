from sympy import *
from axiom.utility import prove, apply
from sympy.stats.symbolic_probability import Probability as P
from axiom import algebra, statistics


# given: P(x, y) = P(x) P(y)
# imply: x | y = x
@apply
def apply(*given):
    equality, inequality = given    
    assert equality.is_Equal
    assert inequality.is_Unequal
    assert inequality.rhs.is_zero
    inequality.lhs.is_Probability 
    x = inequality.lhs.arg
    
    lhs, rhs = equality.args
    assert lhs.is_Probability
    _x, y = lhs.arg.args

    if x != _x:
        _x, y = y, _x
    assert x == _x
    assert rhs == P(x) * P(y)
   
    return Equal(P(y, given=x), P(y))


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    
    given = Equal(P(x, y), P(x) * P(y))
    
    Eq << apply(given, Unequal(P(x), 0))
    
    Eq << Eq[-1].simplify()
    
    Eq << statistics.bayes.corollary.apply(Eq[1], var=y)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Eq[-1] - Eq[-1].rhs
    
    Eq << Eq[-1].this.lhs.collect(P(x))
    
    Eq << algebra.is_zero.imply.ou.apply(Eq[-1])
    
    Eq <<= Eq[-1] & Eq[1]
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])
    

if __name__ == '__main__':
    prove()
