from sympy.functions.combinatorial.factorials import binomial
from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Equality
import axiom
from sympy.concrete.expr_with_limits import Ref
from sympy.concrete.summations import Sum
from sympy.matrices.expressions.determinant import Det
from sympy.concrete.products import Product
from sympy.functions.elementary.piecewise import Piecewise
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.matrices.expressions.matexpr import Identity


@plausible
def apply(a):
    n = a.shape[0]
    i = Symbol('i', integer=True)
    j = Symbol('j', integer=True)

    return Equality(Det(Ref[i:n, j:n](a[j] ** i)), Product[j:i, i:n](a[i] - a[j]))


from sympy.utility import check


def row_transformation(a, *limits):
    n = limits[0][-1] + 1
    (i, *_), (j, *_) = limits
    return Identity(n) - Ref[i:n, j:n](a[0] * KroneckerDelta(i, j + 1))


@check
def prove(Eq):
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    a = Symbol('a', shape=(oo,), zero=False, complex=True)
    
    Eq << apply(a[:n])
    
    Eq << Eq[-1].subs(n, 2).this.rhs.doit(deep=True)
    
    Eq << Eq[-1].this.lhs.arg.as_Matrix().this.lhs.doit()
    
#     Eq << Eq[-1].this.rhs.doit(deep=True).this.rhs.expand()
    
    Eq.deduction = Eq[0].subs(n, n + 1)
    
    D = Eq.deduction.lhs.arg
    
    Eq << (row_transformation(a, *D.limits) @ D).this.expand()
    
    from sympy import S
    
    i, j = Eq[-1].rhs.variables
    Eq << Eq[-1].rhs[i, S.Zero].this.function.expand()
    
    Eq << Eq[-1].this.rhs.function.powsimp()
    
    Eq << Eq[-1].this.rhs.doit()
    
    Eq << Eq[-1].this.rhs.as_two_terms()
    
    k = Eq[-1].rhs.args[1].variable
    Eq << Eq[-1].this.rhs.args[1].limits_subs(k, k - 1)
    
    Eq << Eq[-1].this.rhs.simplify()
    
    
if __name__ == '__main__':
    prove(__file__)
