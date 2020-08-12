from sympy.core.relational import Equality
from sympy.core.symbol import Symbol, dtype
from sympy.utility import check, plausible, Ref
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import Forall, Exists
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap
from sympy.sets.conditionset import conditionset
from sympy.functions.special.tensor_functions import KroneckerDelta


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
    
    p = Symbol('p', shape=(n,), integer=True, nonnegative=True)
    
    P = Symbol('P', dtype=dtype.integer * n, definition=conditionset(p, Equality(p.set_comprehension(), Interval(0, n - 1, integer=True))))
    
    return Forall(Contains(Ref[k:n](x[p[k]]), S), (p, P), given=given)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    S = Symbol('S', dtype=dtype.integer * n)    
    
    x = Symbol('x', **S.element_symbol().dtype.dict)
    
    i = Symbol('i', domain=Interval(0, n - 1, integer=True))
    j = Symbol('j', domain=Interval(0, n - 1, integer=True))    
    
    w = Symbol('w', integer=True, shape=(n, n, n, n), definition=Ref[i, j](Swap(n, i, j)))
    
    k = Symbol('k', domain=Interval(0, n - 1, integer=True))
    
    given = Forall(Contains(Ref[k:n](x[(w[i, j] @ Ref[k:n](k))[k]]), S), (x, S))
    
    Eq.P_definition, Eq.w_definition, Eq.swap, Eq.axiom = apply(given)
    
    Eq << Eq.swap.subs(j, i)
    
    Eq << Eq.w_definition.subs(j, i)[k] @ Ref[k](k)
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[0].subs(Eq[-1])

    p = Eq.P_definition.rhs.variable
    
    Eq << Eq.swap.subs(i, p[0]).subs(j, 0)    
    
    y = Symbol('y', shape=(n, n), integer=True)
#     the changing indices of previous arrangement
    r = Symbol('r', shape=(n, n), integer=True)
    
    Eq.r0_definition = Equality.define(r[0], Ref[k](k))
    
    d = Symbol('d', shape=(n,), definition=Ref[j](Ref[k](KroneckerDelta(r[j, k], j)) @ Ref[k](k)))
    
    Eq.d_definition = d.equality_defined()
    
    Eq.r_definition = Equality.define(r[j + 1], w[p[j], d[j]] @ r[j], given=Eq.r0_definition)
    
    Eq.d_assertion = Equality(r[j, d[j]], j, plausible=True)
    Eq.d0_assertion = Eq.d_assertion.subs(j, 0)
    
    Eq.d_definition_expand = Eq.d_definition.this.rhs.expand()
    
    Eq << Eq.d_definition_expand.subs(j, 0).subs(Eq.r0_definition[Eq.d_definition_expand.rhs.variable])    

    Eq << (Eq.r0_definition[d[0]] - Eq.d0_assertion).reversed  
    
    Eq.d_assertion_induction = Eq.d_assertion.subs(j, j + 1)
    Eq << Eq.d_definition_expand.subs(j, j + 1)
    Eq << Eq.r_definition[Eq[-1].rhs.variable]
    
    Eq << Eq[-2].subs(Eq[-1])
    return
    Eq.y0_definition = Equality.define(y[0], x)
    Eq.y_definition = Equality.define(y[j + 1], Ref[k](y[j][(w[p[j], d[j]] @ Ref[k](k))[k]]), given=Eq.y0_definition)
    
    Eq << Eq.y_definition.subs(j, 0)
    
    Eq.y1_definition = Eq[-1][0]

    Eq << Eq.w_definition.subs(i, p[0]).subs(j, d[0])[k] @ Ref[k](k)

    Eq << Eq[-1].this.rhs.expand().subs(k, 0)
    
    Eq << Eq.d_definition.subs(j, 0)
    return
    
    Eq << Eq.y1_definition.subs(Eq[-1]).subs(Eq.y0_definition[p[0]])

    t = Symbol('t', domain=Interval(1, n, integer=True))    
    Eq << Forall(Exists(Equality(y[t, j], x[p[j]]), (y,)), (j, 0, t - 1), plausible=True)

        
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
