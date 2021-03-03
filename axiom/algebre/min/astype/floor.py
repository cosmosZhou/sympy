from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(self): 
    args = axiom.is_Min(self)
    
    x = []
    for arg in args: 
        if arg.is_Floor:
            arg = arg.arg
        elif arg.is_Plus:
            flrs = []
            non_flrs = []
            for i, flr in enumerate(arg.args):
                if flr.is_Floor:
                    flrs.append(flr)
                else:
                    non_flrs.append(flr)
                    
            assert flrs
            arg = Plus(*non_flrs)
            assert arg.is_integer
            
            for f in flrs:
                arg += f.arg
        else:
            return                      
        x.append(arg)
        
    return Equality(self, Floor(Min(*x)))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    n = Symbol.n(integer=True)

    Eq << apply(Min(n + floor(x), floor(y)))
    
    Eq << Eq[0].apply(algebre.equal.given.et.where.floor)
    
    assert n + floor(x) <= n + x
    
    Eq <<= algebre.imply.strict_less_than.floor.apply(x) + n, algebre.imply.strict_less_than.floor.apply(y)
    
    Eq << algebre.strict_less_than.strict_less_than.imply.strict_less_than.min.both.apply(Eq[-2], Eq[-1])
    
    Eq << Eq[-1].this.rhs.apply(algebre.min.astype.plus)
    
    Eq << Eq[-1] - 1
    
if __name__ == '__main__':
    prove(__file__)
