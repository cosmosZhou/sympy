from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, *, cond=None):
    or_eqs = axiom.is_Or(given)
    
    new_or_eqs = []
    
    and_eqs = []
    for and_eq in or_eqs:
        if and_eq.is_And:
            try:
                i = and_eq.args.index(cond)
                args = [*and_eq.args]
                del args[i]
                and_eqs.append(And(*args))
                continue
            except:
                ...
        new_or_eqs.append(and_eq)
        
    assert not new_or_eqs    
    assert and_eqs 
    
    return And(Or(*and_eqs), cond)           


@prove
def prove(Eq):
    k = Symbol.k(integer=True, positive=True)
    x = Symbol.x(real=True, shape=(k,), given=True)
    y = Symbol.y(real=True, shape=(k,), given=True)
    
    f = Function.f(shape=(k,), real=True)
    h = Function.h(shape=(k,), real=True)
    g = Function.g(shape=(k,), real=True)
    
    Eq << apply(Or(Unequal(x, y) & (y > 0), Equal(f(x), g(y)) & (y > 0), Equal(h(x), g(y)) & (y > 0)), cond=y > 0)
    
    Eq << algebra.et.imply.ou.apply(Eq[1], simplify=False)
    

if __name__ == '__main__':
    prove()

