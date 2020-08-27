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
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.matrices.expressions.matexpr import Identity
from axiom.Algebre import matrix


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
    
    Eq.deduction = Eq[0].subs(n, n + 1)
    
    D = Eq.deduction.lhs.arg
    
    Eq << (row_transformation(a, *D.limits) @ D).this.expand()
    
    Eq << matrix.determinant.expansion_by_minors.apply(Eq[-1].rhs, i=0)
    
    Eq << Eq[-1].this.rhs.bisect(front=1)
    
    Eq << Eq[-1].this.rhs.args[0].args[0].arg.simplify(deep=True)
    
    Eq << Eq[-1].this.rhs.args[0].args[1].doit()
    
    Eq.recursion = Eq[-1].this.rhs.args[1].function.args[-1].doit()
    
    Eq << Eq.recursion.rhs.args[0].arg.this.function.doit()
    
    Eq << Eq[-1].this.rhs.simplify(deep=True, wrt=Eq[-1].rhs.variable)
    
    Eq << Eq[-1].this.function.rhs.expand().this.function.rhs.collect(Eq[-1].rhs.args[1].args[-1])
    
    
if __name__ == '__main__':
    prove(__file__)
# git clone https://github.com/sympy/sympy.git
