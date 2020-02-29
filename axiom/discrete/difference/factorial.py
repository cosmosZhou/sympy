from sympy.functions.combinatorial.factorials import factorial
from sympy.core.relational import Equality
from sympy.utility import plausible, Difference
from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from axiom import discrete


@plausible
def apply(x, n):
    if not isinstance(x, Symbol):
        return
    return Equality(Difference[x, n](x ** n), factorial(n))


from sympy.utility import check


@check
def prove(Eq):
    x = Symbol('x')
    n = Symbol('n', integer=True, nonnegative=True)
    Eq << apply(x, n)
    Eq << Eq[0].subs(n, 0).doit()
    Eq << Eq[0].subs(n, n + 1)
    Eq << Eq[-1].this.lhs.bisect(back=1)

    Eq << Eq[-1].this.lhs.expr.doit()
    Eq << discrete.combinatorics.binomial.theorem.apply(x, 1, n + 1) - x ** (n + 1)

    Eq << Eq[-1].this.rhs.args[1].bisect(back=1)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.as_Sum()

    Eq << Eq[-1].this.lhs.bisect(back=1)

    Eq << Eq[-1].subs(Eq[0])

    Eq << discrete.combinatorics.factorial.expand.apply(n + 1)

    Eq.equation = Eq[-2].this.rhs.subs(Eq[-1])

    k = Eq.equation.lhs.limits[0][0]
    k = Symbol(k.name, integer=True, domain=Interval(0, n, right_open=True))
    
    Eq << Eq[0].subs(n, k)
    Eq << Difference[x, n - k](Eq[-1])
    Eq << Eq[-1].this.lhs.as_one_term()    
    Eq << Eq[-1].forall(k)
    
    Eq << Eq.equation.subs(Eq[-1])
    

if __name__ == '__main__':
    prove(__file__)

