from axiom.utility import plausible
from sympy.logic.boolalg import Or
from sympy.sets.contains import Contains
from sympy.core.relational import Equality
from sympy import Symbol
from axiom import sets
from sympy.functions.elementary.piecewise import Piecewise
from sympy.sets.sets import Interval
from sympy.core.function import Function


# given: A in B 
# => A | B = B
@plausible
def apply(given, s, f, g):
    assert given.is_Contains
    x, S = given.args
    assert s in S
    return Equality(Piecewise((f, Contains(x, s)), (g, True)), Piecewise((g, Contains(x, S - s)), (f, True)).simplify(), given=given)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(integer=True)
    f = Function.f(nargs=(1,), shape=())
    g = Function.g(nargs=(1,), shape=())
    Eq << apply(Contains(x, Interval(0, n, integer=True)), Interval(1, n, integer=True), f(x), g(x))
    
    x = Symbol.x(domain=Eq[0].rhs)
    Eq << Contains(x, Eq[0].rhs, plausible=True)
    
    Eq << Eq[1].subs(Eq[0].lhs, x)
    
    Eq << Eq[-1].this.lhs.args[0].cond.simplify()
    
    Eq << Eq[-1].forall((x,))
    
    Eq << Eq[-1].astype(Or)
    
    Eq << (Eq[-1] & Eq[0]).split()
    

if __name__ == '__main__':
    prove(__file__)

