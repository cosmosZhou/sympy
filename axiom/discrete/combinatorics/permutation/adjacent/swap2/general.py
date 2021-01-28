from sympy.core.relational import Equality
from sympy.core.symbol import dtype
from axiom.utility import prove, apply

from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.functions.elementary.piecewise import Piecewise
from sympy import ForAll, LAMBDA
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap

from sympy import Symbol
from axiom import algebre, discrete


@apply(imply=True)
def apply(given):
    assert given.is_ForAll and len(given.limits) == 2
    j, a, n_munis_1 = given.limits[0]
    assert a == 1
    x, S = given.limits[1]
    
    contains = given.function
    assert contains.is_Contains
    ref, _S = contains.args
    assert S == _S and ref.is_LAMBDA and S.is_set
    dtype = S.etype
    
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
    
    n = n_munis_1
    
    assert x[j] == xj and x[i] == xi and x[0] == x0 and dtype == x.type    
    
    w = Symbol.w(definition=LAMBDA[j, i](Swap(n, i, j)))
    
    return ForAll(Contains(w[i, j] @ x, S), (x, S))


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    S = Symbol.S(etype=dtype.integer * n)    
    
    x = Symbol.x(**S.element_symbol().type.dict)
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    
    given = ForAll(Contains(LAMBDA[i:n](Piecewise((x[0], Equality(i, j)), (x[j], Equality(i, 0)), (x[i], True))), S), (j, 1, n), (x, S))
    
    Eq << apply(given)
    
    w = Eq[0].lhs.base
    
    Eq << discrete.combinatorics.permutation.adjacent.swap1.helper.apply(x, w[0])
    
    Eq << algebre.equal.imply.equal.lamda.apply(Eq[-1], (i, 0, n), simplify=False)
    
    Eq.given = Eq[1].subs(Eq[-1].reversed)
    
    Eq << discrete.matrix.elementary.swap.identity.apply(x, w)
    
    Eq << Eq[-1].subs(Eq[-1].rhs.args[0].indices[0], 0)
    
    Eq << Eq[-1].this.lhs.limits_subs(Eq[-1].lhs.variable, i)
    
    Eq << Eq[-1].this.lhs.function.indices[0].args[1].limits_subs(Eq[-1].lhs.function.indices[0].args[1].variable, i)
    
    Eq.given = Eq.given.subs(Eq[-1])
    
    Eq << Eq.given.limits_swap()
    
    Eq << ForAll[x:S](Eq[-1].function.subs(j, 0), plausible=True)
    
    Eq << Eq[-1].subs(w[0, 0].this.definition)
    
    Eq <<= Eq[-1] & Eq[-2]
    
    Eq << discrete.combinatorics.permutation.adjacent.swap2.contains.apply(Eq[-1])
        

if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
