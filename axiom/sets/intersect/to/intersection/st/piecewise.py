from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom


@apply
def apply(self):
    fx, *limits = axiom.is_INTERSECTION(self)
    * limits, limit = limits
    if limits:
        ecs = ((INTERSECTION(e, *limits).simplify(), c) for e, c in fx.args)
        fx = Piecewise(*ecs)
    
    return Equal(self, fx.as_multiple_terms(*axiom.limit_is_set((limit,)), cls=INTERSECTION))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(etype=dtype.real)
    g = Function.g(etype=dtype.real)
    F = Function.F(etype=dtype.real)
     
    Eq << apply(INTERSECTION[y:F(x), x:B](Piecewise((f(x, y), Contains(x, A)), (g(x, y), True))))
    
    Eq << INTERSECTION[y:F(x)](Piecewise((f(x, y), Contains(x, A)), (g(x, y), True))).this.apply(sets.intersect.to.piecewise)
    
    Eq << sets.eq.imply.eq.intersection_comprehension.apply(Eq[-1], (x, B))
    
    Eq << Eq[-1].this.rhs.apply(sets.intersect.to.intersection.single_variable)

if __name__ == '__main__':
    prove()

