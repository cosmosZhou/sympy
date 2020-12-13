from sympy.core.relational import Equality, Unequal
from axiom.utility import plausible
from sympy.core.symbol import dtype
from sympy.sets.sets import Union, Intersection
from sympy import Symbol
from axiom import sets, algebre
from sympy.concrete.summations import Sum
from sympy.functions.elementary.piecewise import Piecewise
from sympy.sets.contains import Contains
from sympy.sets.conditionset import conditionset
from sympy.concrete.forall import ForAll

# reference
# www.cut-the-knot.org/arithmetic/combinatorics/InclusionExclusion.shtml


@plausible
def apply(a, wrt=None):
    if wrt is None:
        wrt = a.generate_free_symbol(**a.type.dict)
    U = a.universalSet
    return Equality(conditionset(wrt, Unequal(wrt, a)), U - a.set)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))

    Eq << apply(x)
    
    A = Symbol.A(definition=Eq[0].lhs)
    B = Symbol.B(definition=Eq[0].rhs)
    
    a = Eq[0].lhs.variable
    Eq.forall_contains_in_B = ForAll[a:A](Contains(a, B), plausible=True)
    
    Eq << Eq.forall_contains_in_B.this.limits[0][1].definition
    
    Eq << Eq[-1].this.function.rhs.definition
    
    Eq.forall_contains_in_A = ForAll[a:B](Contains(a, A), plausible=True)
    
    Eq << Eq.forall_contains_in_A.this.limits[0][1].definition
    
    Eq << Eq[-1].this.function.rhs.definition
    
    Eq << ForAll[a:Eq[-1].function.invert()](Eq[-1].limits_condition.invert(), plausible=True)
    
    Eq << Eq[-1].this.function.simplify()
    
    Eq << algebre.forall.imply.forall.limits_swap.apply(Eq[-1])

    Eq << sets.forall_contains.forall_contains.imply.equality.apply(Eq.forall_contains_in_A, Eq.forall_contains_in_B)
    
    Eq << Eq[-1].this.lhs.definition
    Eq << Eq[-1].this.rhs.definition
    
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    prove(__file__)

