from axiom.utility import plausible
from sympy.core.relational import LessThan
from sympy import Symbol
import axiom
from sympy.functions.elementary.miscellaneous import Max
from axiom import algebre, sets


@plausible
def apply(*given):
    greater_than, less_than = given
    x, m = axiom.is_GreaterThan(greater_than)
    _x, M = axiom.is_LessThan(less_than)
    assert x == _x
    
    return LessThan(x * x, Max(m * m, M * M))


from axiom.utility import check


@check
def prove(Eq):
    x = Symbol.x(real=True, given=True)
    m = Symbol.m(real=True, given=True)
    M = Symbol.M(real=True, given=True)
    
    Eq << apply(x >= m, x <= M)
    
    Eq << Eq[-1].bisect(x >= 0).split()
    
    Eq << Eq[1].bisect(x >= 0).split()
    
    Eq << algebre.ou.imply.ou.invert.apply(Eq[-2])
    
    Eq << Eq[-1].this.args[1].apply(sets.contains.imply.less_than.square.nonnegative_interval)
    
    Eq << Eq[-1].this.args[1].apply(algebre.less_than.imply.less_than.transit, Eq[2].rhs)
    
    Eq << Eq[0].bisect(x > 0).split()
    
    Eq << algebre.ou.imply.ou.invert.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[1].apply(sets.contains.imply.less_than.square.nonpositive_interval)
    
    Eq << Eq[-1].this.args[1].apply(algebre.less_than.imply.less_than.transit, Eq[2].rhs)
    
    Eq << Eq[-1].this.args[0].apply(algebre.strict_greater_than.imply.greater_than)

    
if __name__ == '__main__':
    prove(__file__)
