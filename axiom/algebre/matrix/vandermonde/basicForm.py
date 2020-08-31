from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Equality
from sympy.concrete.expr_with_limits import Ref
from sympy.matrices.expressions.determinant import Det
from sympy.concrete.products import Product
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.matrices.expressions.matexpr import Identity
from axiom.algebre import matrix


@plausible
def apply(a):
    n = a.shape[0]
    i = Symbol('i', integer=True)
    j = Symbol('j', integer=True)

    return Equality(Det(Ref[j:n, i:n](a[j] ** i)), Product[j:i, i:n](a[i] - a[j]))


from sympy.utility import check


def row_transformation(a, *limits):
    n = limits[0][-1] + 1
    (i, *_), (j, *_) = limits
    return Identity(n) - Ref[j:n, i:n](a[0] * KroneckerDelta(i, j + 1))


@check
def prove(Eq):
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    a = Symbol('a', shape=(oo,), zero=False, complex=True)
    
    Eq << apply(a[:n])
    
    Eq << Eq[-1].subs(n, 2).this.rhs.doit(deep=True)
    
    Eq << Eq[-1].this.lhs.arg.as_Matrix().this.lhs.doit()
    
    Eq.deduction = Eq[0].subs(n, n + 1)
    
    D = Eq.deduction.lhs.arg
    
    Eq.expand = (row_transformation(a, *D.limits) @ D).this.expand()
    
    Eq << matrix.determinant.expansion_by_minors.apply(Eq.expand.rhs, i=0)
    
    Eq << Eq[-1].this.rhs.bisect(front=1)
    
    Eq << Eq[-1].this.rhs.args[0].args[0].arg.simplify(deep=True)
    
    Eq << Eq[-1].this.rhs.args[0].args[1].doit()
    
    Eq.recursion = Eq[-1].this.rhs.args[1].function.args[-1].doit()
    
    Eq << Eq.recursion.rhs.args[0].arg.this.function.doit()
    
    Eq << Eq[-1].this.rhs.simplify(deep=True, wrt=Eq[-1].rhs.variable)
    
    Eq << Eq[-1].this.function.rhs.expand().this.function.rhs.collect(Eq[-1].rhs.args[1].args[-1])
    
    Eq.recursion = Eq.recursion.subs(Eq[-1])
    
    Eq << Eq.recursion.rhs.args[1].function.args[1].arg.this.function.args[0].expr.doit()
    
    Eq << Eq[-1].this.rhs.simplify(deep=True, wrt=Eq[-1].rhs.variable)
    
    Eq << Eq[-1].this.function.rhs.args[0].expr.expand().this.function.rhs.args[0].expr.collect(Eq[-1].rhs.args[0][0].args[1].args[-1])
    
    Eq.recursion = Eq.recursion.subs(Eq[-1])
    
    Eq << Eq.recursion.rhs.args[0].arg.this.as_two_terms()
    
    Eq << Eq[-1].det()
    
    var = Eq[-1].rhs.args[1].variable
    Eq.determinant = Eq[-1].this.rhs.args[1].limits_subs(var, var - 1)
    
    k, _ = Eq.determinant.lhs.arg.variables
    j, i = Eq[0].lhs.arg.variables
    
    Eq << Eq[0].this.lhs.arg.limits_subs(j, k).this.lhs.arg.limits_subs(i, j).subs(a[:n], a[1:n + 1])

#     Eq << Eq[-1].this.rhs.limits_subs(i + 1, i).this.rhs.limits_subs(j + 1, j)
    Eq << Eq[-1].this.rhs.limits_subs(i, i - 1)
    
    Eq << Eq[-1].this.rhs.limits_subs(j, j - 1)
    
    Eq << Eq.determinant.subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.as_one_term()
    
    Eq << Product[j:i, i:n + 1](Eq[0].rhs.function).this.bisect(front=1)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq.recursion = Eq.recursion.subs(Eq[-1])
    
    D = Eq.recursion.rhs.args[1].function.args[1].arg
    _i = i.copy(integer=True, positive=True)
    D = D._subs(i, _i)    
    Eq << matrix.determinant.expansion_by_minors.apply(D, j=0).forall(_i)
    
    Eq << Eq.recursion.subs(Eq[-1])
    
    Eq << Eq.expand.det().subs(Eq[-1])
        
if __name__ == '__main__':
    prove(__file__)
# git clone https://github.com/sympy/sympy.git

