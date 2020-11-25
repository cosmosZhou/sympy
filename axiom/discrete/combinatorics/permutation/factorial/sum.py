from sympy.functions.combinatorial.factorials import factorial, binomial
from sympy.core.relational import Equality
from axiom.utility import plausible

from sympy import Symbol
from sympy.concrete.summations import Sum
from axiom.discrete import difference


@plausible
def apply(n):
    i = Symbol.i(integer=True)
    return Equality(factorial(n), Sum[i:0:n]((-1) ** (n - i) * i ** n * binomial(n, i)))


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(n)

    x = Symbol.x(real=True)
    
    Eq << difference.definition.apply(x ** n, x, n)
    
    Eq << difference.factorial.apply(x, n)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].subs(x, 0)
    
    Eq << Eq[-1].this.rhs.simplify()

if __name__ == '__main__':
    prove(__file__)
