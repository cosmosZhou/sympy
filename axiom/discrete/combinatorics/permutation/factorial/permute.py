from sympy.functions.combinatorial.factorials import factorial
from sympy.core.relational import Equality
from sympy.core.symbol import dtype
from axiom.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.functions.elementary.piecewise import Piecewise
from sympy.concrete.expr_with_limits import UNION, ForAll, LAMBDA
from sympy.sets.contains import Contains, Subset
from sympy import Symbol
from axiom import discrete, sets
from sympy.core.function import Function
from sympy.sets.conditionset import conditionset


@plausible
def apply(given):
    assert len(given) == 2
    assert given[0].is_ForAll and len(given[0].limits) == 2
    j, a, n_munis_1 = given[0].limits[0]
    assert a == 1
    x, S = given[0].limits[1]
    
    contains = given[0].function
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
    
    n = n_munis_1 + 1
    
    assert x[j] == xj and x[i] == xi and x[0] == x0 and dtype == x.type
    
    assert given[1].is_ForAll and len(given[1].limits) == 1
    _x, _S = given[1].limits[0]
    assert x == _x and S == _S
    
    equality = given[1].function
    assert equality.is_Equality and {*equality.args} == {abs(x.set_comprehension()), n}
        
    return Equality(abs(S), factorial(n) * abs(UNION[x:S]({x.set_comprehension()})),
                    given=given)


@check
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    S = Symbol.S(etype=dtype.integer * n)    
    
    x = Symbol.x(**S.element_symbol().type.dict)
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    
    given = [ForAll[j:1:n - 1, x:S](Contains(LAMBDA[i:n](Piecewise((x[0], Equality(i, j)), (x[j], Equality(i, 0)), (x[i], True))), S)),
             ForAll[x:S](Equality(abs(x.set_comprehension()), n))]
    
    Eq << apply(given)
    
    Eq << discrete.combinatorics.permutation.adjacent.swap2.general.apply(Eq[0])
    
    Eq.permutation = discrete.combinatorics.permutation.adjacent.swapn.permutation.apply(Eq[-1])
    
    Eq << Eq.permutation.limits[0][1].this.definition
    
    Eq << discrete.combinatorics.permutation.factorial.definition.apply(n)
    
    Eq << Eq[-1].this.lhs.arg.limits_subs(Eq[-1].lhs.arg.variable, Eq[-2].rhs.variable)
    
    Eq <<= Eq[-1] & Eq[-2].abs()
    
    F = Function.F(nargs=(), etype=dtype.integer * n)
    F.eval = lambda e: conditionset(x, Equality(x.set_comprehension(), e), S)
    
    e = Symbol.e(etype=dtype.integer)
    Eq << Subset(F(e), S, plausible=True)
    Eq << Eq[-1].this.lhs.definition
    
    Eq << sets.subset.forall.imply.forall.apply(Eq[-1], Eq.permutation)
    
    Eq.forall_x = ForAll(Contains(Eq[-1].lhs, F(e)), *Eq[-1].limits, plausible=True)
    
    Eq << Eq.forall_x.definition.split()
    
    P = Eq[-1].limits[0][1]
    Eq << sets.imply.conditionset.apply(P)
    Eq << Eq[-1].apply(sets.equality.imply.equality.permutation, x)
    
    Eq.equality_e = Eq[-3] & Eq[-1]
    
    Eq << sets.imply.conditionset.apply(F(e)).reversed
    
    hat_S = Symbol("\hat{S}", definition=Eq[2].rhs.args[0].arg)
    Eq.hat_S_definition = hat_S.this.definition
    
    Eq << Equality(S, UNION[e:hat_S](F(e)), plausible=True)
#     return
    Eq << Eq[-1].subs(Eq.hat_S_definition)
    
    Eq << Eq[-1].this.rhs.function.definition

    

if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
