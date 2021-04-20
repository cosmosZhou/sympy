from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom


@apply
def apply(self):
    intersection, *limits = axiom.is_UNION(self)
    x, S = axiom.limit_is_set(limits)
    piecewise, gx = axiom.is_Intersection(intersection)
    if not piecewise.is_Piecewise:
        piecewise, gx = gx, piecewise
                
    ecs = ((e & gx, c) for e, c in axiom.is_Piecewise(piecewise))
    
    return Equal(self, Piecewise(*ecs).as_multiple_terms(x, S, UNION))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    C = Symbol.C(etype=dtype.integer)
    
    x = Symbol.x(integer=True)
    f = Function.f(etype=dtype.real)
    h = Function.h(etype=dtype.real)
    g = Function.g(etype=dtype.real)

    Eq << apply(UNION[x:A](Intersection(Piecewise((f(x), Contains(x, C)), (h(x), True)), g(x), evaluate=False)))
    
    Eq << Eq[0].this.lhs.function.apply(sets.intersection.to.piecewise)
    
    Eq << Eq[-1].this.lhs.apply(sets.union_comprehension.to.union.st.piecewise)


if __name__ == '__main__':
    prove()

