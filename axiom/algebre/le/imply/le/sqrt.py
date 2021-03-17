from axiom.utility import prove, apply
from sympy.core.relational import Equality, LessThan
from sympy import Symbol, ForAll, Slice, Sum
from sympy.core.function import Function
import axiom
from sympy.concrete.limits import limits_dict
from sympy.sets.sets import Interval
from axiom import algebre, sets
from sympy.core.symbol import dtype
from sympy.core.numbers import oo


@apply
def apply(given):
    lhs, rhs = axiom.is_LessThan(given)
    
    lhs = axiom.is_Squared(lhs)
    rhs = axiom.is_Squared(rhs)
    
    assert lhs.is_real
    assert rhs.is_real
    
    return LessThan(abs(lhs), abs(rhs))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    
    Eq << apply(LessThan(x * x, y * y))
    
    Eq << Eq[0] - Eq[0].rhs
    
    Eq << Eq[-1].this.lhs.factor()
    
    Eq << algebre.is_nonpositive.imply.ou.having.multiply.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[0].args[0] - y
    
    Eq << Eq[-1].this.args[0].args[0] - y
    
    Eq << Eq[-1].this.args[0].args[0] + y
    
    Eq << Eq[-1].this.args[0].args[0] + y
    
    Eq << Eq[-1].this.args[0].apply(algebre.le.ge.imply.le.abs.both)
    
    Eq << Eq[-1].this.args[0].apply(algebre.le.ge.imply.le.abs.both)
    
    

if __name__ == '__main__':
    prove(__file__)

