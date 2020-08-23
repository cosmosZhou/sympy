from sympy.core.symbol import Symbol, generate_free_symbol
from sympy.functions.combinatorial.factorials import binomial, factorial
from sympy.core.relational import Equality
from sympy.utility import plausible

from sympy.functions.combinatorial.numbers import Stirling
from axiom.discrete.combinatorics import stirling
import axiom
from axiom.discrete import difference
from axiom import discrete
from sympy.concrete.summations import Sum
from sympy.concrete.expr_with_limits import Ref


@plausible
def apply(n, k):
    free_symbols = n.free_symbols | k.free_symbols
    i = generate_free_symbol(free_symbols, integer=True)
    return Equality(Stirling(n, k), Sum[i:0:k]((-1) ** (k - i) * binomial(k, i) * i ** n) / factorial(k))


from sympy.utility import check


@check
def prove(Eq):
    k = Symbol('k', integer=True, nonnegative=True)
    n = Symbol('n', integer=True, nonnegative=True)
    Eq << apply(n, k)

    Eq << Eq[-1].subs(k, 0).doit()

    Eq << stirling.second.recurrence.apply(n, k)

    Eq << Eq[-1].subs(Eq[0])

    from sympy import oo
    y = Symbol('y', shape=(oo,), definition=Ref[n](Stirling(n, k + 1)))

    Eq << y.equality_defined()

    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-3].subs(Eq[-1].reversed, Eq[-2].reversed)

    Eq << Eq[-1].rsolve(y[n])

    Eq.stirling_solution = Eq[-1].subs(Eq[3])

    Eq << Eq.stirling_solution.subs(n, k + 1)

    Eq << Eq[-1].this.function.solve(Eq[-1].variable)

    Eq.exist_C0 = Eq[-1].this.function.rhs.powsimp(deep=True)

    l = Eq[0].rhs.args[1].limits[0][0]
    Eq << binomial(k + 1, l).this.rewrite(factorial)

    Eq.factorial_expand_kl = axiom.discrete.combinatorics.factorial.expand.apply(k - l + 1)

    Eq << Eq[-1].subs(Eq.factorial_expand_kl)

    Eq << Eq[-1] / factorial(k + 1)

    Eq << Eq[-1].reversed

    Eq.factorial_expand = axiom.discrete.combinatorics.factorial.expand.apply(k + 1)

    Eq << Eq.exist_C0.subs(Eq.factorial_expand, Eq[-1])

    Eq << Eq[-1].this.function.rhs.expand(deep=False)

    Eq.exist_C0 = Eq[-1].this.function.rhs.powsimp()
    
    Eq.exist_C0 = Eq.exist_C0.subs(Eq.factorial_expand_kl.reversed)        

    x = Symbol('x', real=True)

    Eq << difference.definition.apply(x ** (k + 1), x, k + 1)

    Eq << difference.factorial.apply(x, k + 1)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].subs(x, 0)

    Eq << Eq[-1] * (-1) ** (k + 1)

    Eq << Eq[-1].this.rhs.distribute()

    Eq << Eq[-1].this.rhs.bisect(back=1)

    Eq << Eq[-1] - Eq[-1].rhs.args[0]

    Eq << Eq[-1].this.rhs.rewrite(factorial) / factorial(k + 1)
    
    Eq << Eq[-1].this.rhs.powsimp(deep=True)
    
    Eq << Eq.exist_C0.subs(Eq[-1].reversed, Eq.factorial_expand)

    Eq << Eq[-1].this.function.rhs.expand()

    Eq << Eq[-1].this.function.rhs.ratsimp()

    Eq << Eq[-1].subs(Eq.factorial_expand.this.rhs.expand().reversed)

    Eq.stirling_solution = Eq.stirling_solution.subs(Eq[-1])

    Eq << discrete.combinatorics.binomial.expand.apply(k + 1, k - l + 1)
    Eq << discrete.combinatorics.binomial.complement.apply(k, l)
    Eq << discrete.combinatorics.binomial.complement.apply(k + 1, l)

    Eq << Eq[-3].subs(Eq[-1].reversed, Eq[-2].reversed)

    Eq << Eq[-1] / (k + 1)

    Eq << Eq.stirling_solution.subs(Eq[-1].reversed)

    Eq << Eq[-1].subs(Eq.factorial_expand.reversed)

    Eq << Eq[-1] * factorial(k + 1)
    Eq << Eq[-1].expand()

    Eq << Eq[-1].this.rhs.args[0].distribute()

    Eq << Eq[0].subs(k, k + 1) * factorial(k + 1)

    Eq << Eq[-1].this.rhs.bisect(back=1)


if __name__ == '__main__':
    prove(__file__)
