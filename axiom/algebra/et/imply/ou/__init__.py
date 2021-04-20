from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(self):
    for i, eq in enumerate(self.args):
        if isinstance(eq, Or):
            args = [*self.args]
            del args[i]
            this = self.func(*args)
            return Or(*((arg & this).simplify() for arg in eq.args))


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
    
    Eq << apply(And((a < b) | (c < d), (f(x) < g(y))))
    
    Eq << ~Eq[-1]
    
    Eq << algebra.et.imply.cond.apply(Eq[0])
    
    Eq << algebra.cond.cond.imply.cond.apply(Eq[-1], Eq[-3], invert=True)
    
    Eq <<= Eq[-1] & Eq[-3]
    
    

if __name__ == '__main__':
    prove()

del collect
from . import collect
