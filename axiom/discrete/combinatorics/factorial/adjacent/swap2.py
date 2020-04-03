from sympy.functions.combinatorial.factorials import factorial
from sympy.core.relational import Equality
from sympy.core.symbol import Symbol, dtype
from sympy.utility import check, plausible, Ref, Union
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.functions.elementary.piecewise import Piecewise
from sympy.concrete.expr_with_limits import Forall
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap
from axiom.discrete.combinatorics.factorial.adjacent import swap1, swap1_utility


@plausible
def apply(given):
    assert given.is_Forall and len(given.limits) == 2
    j, a, n_munis_1 = given.limits[0]
    assert a == 1
    x, S = given.limits[1]
    
    contains = given.function
    assert contains.is_Contains
    ref, _S = contains.args
    assert S == _S and ref.is_Ref and S.is_set
    dtype = S.element_type
    
    assert len(ref.limits) == 1
    i, a, _n_munis_1 = ref.limits[0]
    assert _n_munis_1 == n_munis_1 and a == 0
    
    piecewise = ref.function
    assert piecewise.is_Piecewise and len(piecewise.args) == 3
    
    x0, condition0 = piecewise.args[0]
    assert condition0.is_Equality and {*condition0.args} == {i, j}
    
    xj, conditionj = piecewise.args[1]
    assert conditionj.is_Equality and {*conditionj.args} == {i, 0}
    
    xi, conditioni = piecewise.args[2]
    assert conditioni
    
    n = n_munis_1 + 1
    
    assert x[j] == xj and x[i] == xi and x[0] == x0 and dtype == x.dtype    
    
    w = IndexedBase('w', integer=True, shape=(n, n, n, n), definition=Ref[i:n, j:n](Swap(n, i, j)))
    
    k = Symbol('k', integer=True)
    return Forall(Contains(Ref[k:n](x[(w[i, j] @ Ref[k:n](k))[k]]), S), (i, 0, n - 1), (j, 0, n - 1), given=given)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    S = Symbol('S', dtype=dtype.integer * n)    
    
    x = IndexedBase('x', **S.element_symbol().dtype.dict)
    
    i = Symbol('i', integer=True)
    j = Symbol('j', integer=True)    
    
    given = Forall(Contains(Ref[i:n](Piecewise((x[0], Equality(i, j)), (x[j], Equality(i, 0)), (x[i], True))), S), (j, 1, n - 1), (x, S))
    
    Eq << apply(given)
    
    w = Eq[0].lhs.base
    
    Eq << swap1_utility.apply(x, w[0])
    
    Eq << Eq[1].subs(Eq[-1].reversed)
    
    k = Eq[2].function.lhs.variable
    Eq << Eq[-1].this.function.lhs.limits_subs(i, k)
    
    Eq << Eq[-1].this.function.lhs.function.args[1].args[1].limits_subs(i, k)    

if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
