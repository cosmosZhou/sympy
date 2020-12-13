from axiom.utility import plausible
from sympy.core.relational import LessThan
from sympy import Symbol, Or
import axiom
from sympy.functions.elementary.miscellaneous import Max
from sympy.functions.elementary.piecewise import Piecewise
from sympy.logic.boolalg import And
from axiom import algebre, sets


@plausible
def apply(*given):
    x_less_than_a, y_less_than_a = given
    x, a = axiom.is_LessThan(x_less_than_a)    
    y, _a = axiom.is_LessThan(y_less_than_a)
    assert a == _a
    return LessThan(Max(x, y), a)


from axiom.utility import check


@check
def prove(Eq):
    a = Symbol.a(real=True, given=True)
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)

    Eq << apply(x <= a, y <= a)
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << Or(And(x <= a, x >= y), And(y <= a, x < y), plausible=True)
    
    Eq << Eq[0].bisect(x >= y).split()
    
    Eq << algebre.ou.imply.ou.invert.apply(Eq[-2])
    
    Eq.ou = Eq[-1].this.args[1].apply(sets.contains.imply.et.interval, simplify=False)
    
    Eq << Eq[1].bisect(x >= y).split()
    
    Eq << algebre.ou.imply.ou.invert.apply(Eq[-1])
    
    Eq << Eq[-1].this.args[1].apply(sets.contains.imply.et.interval, simplify=False)    

    Eq <<= Eq.ou & Eq[-1]
    
    Eq << Eq[-1].astype(Or)
    
    Eq << Eq[-1].this.args[0].astype(Or)
    
    Eq << Eq[-1].this.args[0].args[-1].reversed
    
    Eq << algebre.ou.imply.less_than.two.apply(Eq[4], wrt=a)
    
    Eq << algebre.imply.equality.piecewise.apply(Eq[-1].lhs)
    
    Eq << Eq[-2].subs(Eq[-1])
    
if __name__ == '__main__':
    prove(__file__)
