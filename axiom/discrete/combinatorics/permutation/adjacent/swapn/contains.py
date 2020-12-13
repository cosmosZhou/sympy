from sympy.core.relational import Equality
from sympy.core.symbol import dtype
from axiom.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy import ForAll, LAMBDA
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap
from sympy.sets.conditionset import conditionset
from sympy import Symbol
from axiom import algebre, discrete
from axiom.discrete.combinatorics.permutation.adjacent import swapn


@plausible
def apply(given):
    assert given.is_ForAll
    S = given.rhs
    n = S.etype.shape[0]
    
    ref = given.lhs
    k = ref.variable
    x = ref.function.base
    
    assert len(ref.function.indices) == 1
    index = ref.function.indices[0]
    assert index.is_MatMul and len(index.args) == 2
    
    assert index.args[0].is_Indexed and index.args[1].is_LAMBDA
    
    w = index.args[0].base
    i, j, _k = index.args[0].indices
    
    assert w.definition.is_LAMBDA
    
    (_j, zero, n_1), (_i, _zero, _n_1) = w.definition.limits
    assert zero.is_zero and _zero.is_zero
    
    assert n_1 == _n_1 == n - 1
    assert _k == k and _i == i and _j == j
    assert isinstance(w.definition.function, Swap)
    _n, _i, _j = w.definition.function.args
    assert _n == n and _i == i and _j == j
    
    assert index.args[1].is_LAMBDA and len(index.args[1].limits) == 1 
    
    _k, *_ = index.args[1].limits[0]
    assert _k == k
    
    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True)
    
    P = Symbol.P(etype=dtype.integer * n, definition=conditionset(p[:n], Equality(p[:n].set_comprehension(), Interval(0, n - 1, integer=True))))
    
    return ForAll[p[:n]:P, x:S](Contains(LAMBDA[k:n](x[p[k]]), S))


@check
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    S = Symbol.S(etype=dtype.integer * n)    
    
    x = Symbol.x(**S.element_symbol().type.dict)
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    
    w = Symbol.w(integer=True, shape=(n, n, n, n), definition=LAMBDA[j:n, i:n](Swap(n, i, j)))
    
    k = Symbol.k(integer=True)
    
    given = ForAll[x:S](Contains(LAMBDA[k:n](x[(w[i, j] @ LAMBDA[k:n](k))[k]]), S))
    
    Eq.P_definition, Eq.w_definition, Eq.swap, Eq.axiom = apply(given)

    Eq << discrete.matrix.elementary.swap.identity.apply(x, w)
    
    Eq << Eq.swap.subs(Eq[-1])
    
    Eq << swapn.permutation.apply(Eq[-1])
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
