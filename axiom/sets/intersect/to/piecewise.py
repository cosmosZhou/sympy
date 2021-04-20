from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom


@apply
def apply(self):
    fx, *limits = axiom.is_INTERSECTION(self)    
    ecs = []
    variables = self.variables
    for e, c in axiom.is_Piecewise(fx):
        assert not c.has(*variables)
        ecs.append((INTERSECTION(e, *limits), c))
        
    return Equal(self, Piecewise(*ecs))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    t = Symbol.t(integer=True)
    f = Function.f(etype=dtype.real)
    g = Function.g(etype=dtype.real)
     
    Eq << apply(INTERSECTION[x:A, y:B](Piecewise((f(x, y, t), t > 0), (g(x, y, t), True))))
    
    Eq << algebra.eq.given.ou.apply(Eq[0])
    
    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=0)
    
    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=0, invert=True)

if __name__ == '__main__':
    prove()

