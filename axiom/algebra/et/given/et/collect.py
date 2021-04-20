from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self, *, cond=None):
    matched = []
    unmatch = []
    for eq in self.args:
        if eq.is_Or:
            if cond in eq.args:
                matched.append(Or(*eq._argset - {cond}))
                continue
        elif eq == cond:
            matched.append(S.false)
            continue
        unmatch.append(eq)
    assert unmatch 
    return self.func(*unmatch, Or(cond, self.func(*matched)))            


@prove
def prove(Eq):
    a = Symbol.a(integer=True, given=True)    
    b = Symbol.b(integer=True, given=True)
    
    c = Symbol.c(integer=True, given=True)    
    d = Symbol.d(integer=True, given=True)
    
    x = Symbol.x(real=True, given=True)
    y = Symbol.y(real=True, given=True)
    
    f = Function.f(real=True)
    g = Function.g(real=True)
    
    Eq << apply(((a < b) | (c < d)) & (f(x) < g(y)) & ((x < y) | (c < d)), cond=c < d)
    
    Eq << Eq[1].this.args[0].apply(algebra.ou.imply.et)

if __name__ == '__main__':
    prove()

