from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self, y):
    solution = rsolve(self, y, symbols=True)
    if solution is None:
        return
    solution, limits = solution
    
    eq = self.func(y, solution)
    if len(limits) == 0: 
        return eq
    
    for i, C in enumerate(limits):
        limits[i] = (C,)
    return Exists(eq, *limits)    


@prove(surmountable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)    
    c = Symbol.c(real=True, positive=True)
    i = Symbol.i(domain=Interval(0, k, integer=True))
    
    y = Symbol.y(real=True, shape=(oo,))
    
    Eq << apply(Equal(y[n + 1], y[n] * (k + 1) + i ** n), y=y[n])
    
    
        
if __name__ == '__main__':
    prove()
