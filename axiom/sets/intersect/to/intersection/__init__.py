from sympy import *
from axiom.utility import prove, apply

from axiom import algebra, sets
import axiom


@apply
def apply(self):
    fx, *limits = axiom.is_INTERSECTION(self)
    args = axiom.is_Intersection(fx)

    return Equal(self, Intersection(*(INTERSECTION(arg, *limits) for arg in args)))


@prove
def prove(Eq):
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    x = Symbol.x(integer=True)
    y = Symbol.y(integer=True)
    f = Function.f(etype=dtype.real)
    g = Function.g(etype=dtype.real)
    F = Function.F(etype=dtype.real)

    Eq << apply(INTERSECTION[x:A, y:B](f(x, y) & g(x, y)))
#     Eq << apply(INTERSECTION[x:A](f(x) & g(x)))

    Eq << sets.eq.given.sufficient.apply(Eq[0], wrt=y)

    Eq <<= Eq[-2].this.rhs.apply(sets.contains.given.contains.split.intersection, simplify=False),\
    Eq[-1].this.lhs.apply(sets.contains.imply.contains.split.intersection, simplify=False)

    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.contains.given.forall_contains.st.intersect),\
    Eq[-1].this.lhs.args[0].apply(sets.contains.imply.forall_contains.st.intersect)

    Eq <<= Eq[-2].this.rhs.args[0].apply(sets.contains.given.forall_contains.st.intersect),\
    Eq[-1].this.lhs.args[0].apply(sets.contains.imply.forall_contains.st.intersect)

    Eq <<= Eq[-2].this.rhs.apply(algebra.et.given.forall_et),\
    Eq[-1].this.lhs.apply(algebra.forall.forall.imply.forall_et.limits_intersect)

    Eq <<= Eq[-2].this.lhs.apply(sets.contains.imply.forall_contains.st.intersect),\
    Eq[-1].this.rhs.apply(sets.contains.given.forall_contains.st.intersect)

if __name__ == '__main__':
    prove()

from . import single_variable
from . import st
from . import doit
from . import dissect
