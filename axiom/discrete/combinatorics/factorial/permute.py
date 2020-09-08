from sympy.functions.combinatorial.factorials import factorial
from sympy.core.relational import Equality
from sympy.core.symbol import Symbol, dtype
from sympy.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.functions.elementary.piecewise import Piecewise
from sympy.concrete.expr_with_limits import ForAll, Ref, UNION
from sympy.sets.contains import Contains
from sympy import var

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
    
    assert given[1].is_ForAll and len(given[1].limits) == 1
    _x, _S = given[1].limits[0]
    assert x == _x and S == _S
    
    equality = given[1].function
    assert equality.is_Equality and {*equality.args} == {abs(x.set_comprehension()), n}
        
    return Equality(abs(S), factorial(n) * abs(UNION[x:S]({x.set_comprehension()})),
                    given=given)


@check
def prove(Eq): 
    n = Symbol('n', domain=Interval(2, oo, integer=True))
    S = var(dtype=dtype.integer * n).S    
    
    x = Symbol('x', **S.element_symbol().dtype.dict)
    
    i = var(integer=True).i
    j = var(integer=True).j    
    
    given = [ForAll[j:1:n - 1, x:S](Contains(Ref[i:n](Piecewise((x[0], Equality(i, j)), (x[j], Equality(i, 0)), (x[i], True))), S)),
             ForAll[x:S](Equality(abs(x.set_comprehension()), n))]
    
    Eq << apply(given)


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
