from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets


@apply
def apply(self):
    assert self.is_INTERSECTION
    f = self.function    
    return Equal(self, self.func(Piecewise((f, self.limits_cond), (f.etype.universalSet, True)), *((x,) for x, *_ in self.limits)))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(etype=dtype.real)
     
    Eq << apply(INTERSECTION[x:A, y:B](f(x, y)))    
    
    Eq << Eq[0].this.rhs.function.apply(sets.piecewise.to.union)
    
    Eq << Equal(INTERSECTION[x](Eq[-1].rhs.function), INTERSECTION[x:A](f(x, y) | Eq[-1].rhs.function.args[1]), plausible=True)
    
    Eq << Eq[-1].this.lhs.apply(sets.intersect.simplify.piecewise)
    
    Eq << sets.eq.imply.eq.intersection_comprehension.apply(Eq[-1], (y,))
    
    Eq << Eq[1].this.rhs.subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.apply(sets.intersect.to.intersection.st.piecewise)


if __name__ == '__main__':
    prove()

