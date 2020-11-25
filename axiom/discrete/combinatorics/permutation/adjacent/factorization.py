from sympy.core.relational import Equality
from sympy.core.symbol import dtype
from axiom.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import ForAll, LAMBDA, Exists
from sympy.matrices.expressions.matexpr import Swap
from sympy.sets.conditionset import conditionset
from sympy.concrete.products import MatProduct
from sympy import Symbol, Slice
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.matrices import Matrix
import axiom
from sympy.matrices.expressions.matmul import MatMul
from axiom.algebre.matrix import elementary
from axiom import discrete, sets


@plausible
def apply(n):
    i = Symbol.i(integer=True)
    
    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True)
    
    P = Symbol.P(etype=dtype.integer * n, definition=conditionset(p[:n], Equality(p[:n].set_comprehension(), Interval(0, n - 1, integer=True))))
    
    b = Symbol.b(integer=True, shape=(oo,), nonnegative=True)
    
    return ForAll[p[:n]:P](Exists[b[:n]](Equality(p[:n], LAMBDA[i:n](i) @ MatProduct[i:n](Swap(n, i, b[i])))))


@check
def prove(Eq): 
    n = Symbol.n(domain=[2, oo], integer=True)
    
    Eq << apply(n)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Eq[-1].subs(n, 2)
        
    Eq << Eq[-1].doit(deep=True)    
#     b[0] = 0, b[1] = KroneckerDelta[p[0], 0]
    b = Eq[-2].function.variable
    p0 = Eq[-1].variable
    Eq << Eq[-1].subs(b, Matrix((0, KroneckerDelta(p0, 0))))
    
    Eq.equation = Eq[-1].this.function.rhs.expand()
    
    Eq.limits_assertion = sets.imply.forall.apply(Eq.equation, simplify=False)
    
    Eq << Eq.limits_assertion.sum()
    
    Eq.p1_equality = Eq[-1].this.function - p0
    
    Eq << Eq.equation.subs(Eq.p1_equality) 
    
    Eq.premier, Eq.second = Eq[-1].split()
    
    Eq << Eq.limits_assertion.split()
    
    Eq << Eq[-2].apply(sets.contains.imply.equality.equality0).reversed
    
    Eq << Eq[-1].subs(Eq.p1_equality)
    
    Eq << Eq.premier.subs(Eq.second.reversed)
    
    Eq.plausible = Eq[2].subs(n, n + 1)
    
    Eq << Eq.plausible.function.function.rhs.args[1].this.bisect(Slice[-1:])

    Eq << axiom.algebre.matrix.elementary.swap.concatenate_product.apply(n, n, b)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq.plausible.subs(Eq[-1])
    
    Eq << Eq[-1].this.function.function.rhs.args[0].bisect(Slice[-1:])
    
    Eq << MatMul(*Eq[-1].function.function.rhs.args[:2]).this.expand()
    
    Eq << Eq[-1].subs(Eq[-1].rhs.args[0].this.T)
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq.deduction = Eq[-1].this.function.function @ Eq[-1].function.function.rhs.args[1]
    
    Eq << axiom.discrete.combinatorics.permutation.exists.apply(n + 1)
    
    Eq << Eq[-1].this.function.limits_subs(Eq[-1].function.variable, b[n])
    
    Eq.exists_n = Eq[-1].subs(Eq[-1].limits[0][1].this.definition)
    
    p_quote = Symbol.p_quote(definition=Eq.deduction.function.function.lhs)
    
    Eq.p_quote_definition = p_quote.this.definition
    
    Eq.deduction = Eq.deduction.subs(Eq.p_quote_definition.reversed)
    
    Eq << Eq.p_quote_definition[n]
    
    Eq << Eq[-1].this.rhs.args[1].function.as_KroneckerDelta()
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].subs(Eq.exists_n)
    
    Eq << Eq[-1].this.function().function.rhs.simplify()
    Eq.exists_n_plausible = Eq[-1].this.function.exists((Eq[-1].function.variable,))
    
    Eq << elementary.swap.invariant.permutation.apply(n + 1, left=False)
    
    i, j = Eq[-1].function.lhs.args[1].indices
    Eq << Eq[-1].subs(Eq[-1].function.lhs.args[1].this.definition)
    
    Eq << Eq[-1].subs(i, n).subs(j, b[n]).limits_subs(Eq[-1].variable, Eq.exists_n_plausible.variable).subs(Eq.p_quote_definition.reversed)
    
    Eq << Eq[-1].subs(Eq[-1].function.rhs.this.definition)
    
    Eq << Eq.exists_n_plausible.apply(discrete.combinatorics.permutation.pop_back, Eq[-1])
    
    Eq << Eq[2].subs(Eq[2].variable, p_quote[:n])
    
    Eq << Eq[-1].subs(Eq[-2].reversed)
    
    Eq << Eq.p_quote_definition.lhs.this.bisect(Slice[-1:])
    
    Eq << Eq[-1].subs(Eq[-2])
    
#     assert Eq[-1].equivalent[1].equivalent[0].given.equivalent.equivalent[0] is Eq[1]
#     assert Eq[-1].equivalent[1].equivalent[1].equivalent.given.equivalent[0] is Eq.exists_n_plausible
    Eq << Eq[-1].subs(Eq.exists_n_plausible)   

    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
