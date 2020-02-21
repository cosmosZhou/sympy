from sympy.core.relational import Equality
from sympy.core.symbol import Symbol, dtype
from sympy.utility import check, plausible, Ref
from sympy.tensor.indexed import IndexedBase
from sympy.sets.sets import Interval, Intersection
from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import Forall
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap
from sympy.sets.conditionset import conditionset
from sympy.sets import sets


@plausible
def apply(given):
    assert given.is_Forall
    S = given.rhs
    n = S.element_type.shape[0]
    
    ref = given.lhs
    k = ref.variable
    x = ref.function.base
    
    assert len(ref.function.indices) == 1
    index = ref.function.indices[0]
    assert index.is_MatMul and len(index.args) == 2
    
    assert index.args[0].is_Indexed and index.args[1].is_Ref
    
    w = index.args[0].base
    i, j, _k = index.args[0].indices
    
    assert w.definition.is_Ref
    
    (_i,), (_j,) = w.definition.limits
    assert _k == k and _i == i and _j == j
    assert isinstance(w.definition.function, Swap)
    _n, _i, _j = w.definition.function.args
    assert _n == n and _i == i and _j == j
    
    assert index.args[1].is_Ref and len(index.args[1].limits) == 1 
    
    _k, *_ = index.args[1].limits[0]
    assert _k == k
    
    p = IndexedBase('p', (n,), integer=True, nonnegative=True)
    
    P = Symbol('P', dtype=dtype.integer * n, definition=conditionset(p, Equality(p.set_comprehension(), Interval(0, n - 1, integer=True))))
    
    return Forall(Contains(Ref[k:n](x[p[k]]), S), (p, P), given=given)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    S = Symbol('S', dtype=dtype.integer * n)    
    
    x = IndexedBase('x', **S.element_symbol().dtype.dict)
    
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))    
    
    w = IndexedBase('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Swap(n, i, j)))
    
    k = Symbol('k', domain=Interval(0, n - 1, integer=True))
    
    given = Forall(Contains(Ref[k:n](x[(w[i, j] @ Ref[k:n](k))[k]]), S), (x, S))
    
    Eq.P_definition, Eq.w_definition, Eq.swap, Eq.axiom = apply(given)
    
    p = Eq.axiom.variable
    
    U = Interval(1, n - 1, integer=True)
    A = {k, p[0]}
    print((U - (A & U)) & A)
#     Intersection(Interval.Ropen(1, n) \ Intersection({k, p[0]}, Interval.Ropen(1, n)), {k, p[0]})
    
    Eq << Eq.swap.subs(j, i)
    
    Eq << Eq.w_definition.subs(j, i)[k] @ Ref[k](k)
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[0].subs(Eq[-1])

    p = Eq.P_definition.rhs.variable
    
    Eq << Eq.swap.subs(i, p[0]).subs(j, 0)
    
    Eq << Eq.w_definition.subs(i, p[0]).subs(j, 0)[k] @ Ref[k](k)
    
    Eq << Eq[-1].this.rhs.expand()
    
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
