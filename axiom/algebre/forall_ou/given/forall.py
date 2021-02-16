from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply(imply=True)
def apply(given):
    ou, *limits = axiom.forall_ou(given)
    eqs = ou.args
    
    cond = given.limits_condition
    conds = []
    for eq in eqs:
        if (eq & cond).is_BooleanFalse:
#         if (cond & eq).is_BooleanFalse:
            ...
        else:
            conds.append(eq)
            
    return ForAll(Or(*conds), *limits)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    f = Function.f(shape=(), real=True)
    
    Eq << apply(ForAll[x:2:b]((x <= 1) | (f(x) >= 1)))
#     Eq << apply(ForAll[x:2:b]((x < 2) | (f(x) >= 1)))
#     Eq << apply(ForAll[x:2:b]((x > b) | (f(x) >= 1)))
#     Eq << apply(ForAll[x:2:b]((x >= b + 1) | (f(x) >= 1)))
    
    Eq << ~Eq[-1]
    
    Eq <<= Eq[-1] & Eq[0]    

if __name__ == '__main__':
    prove(__file__)

