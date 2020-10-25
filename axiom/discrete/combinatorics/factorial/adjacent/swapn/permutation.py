from sympy.core.relational import Equality
from sympy.core.symbol import dtype
from axiom.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import ForAll, LAMBDA
from sympy.sets.contains import Contains
from sympy.matrices.expressions.matexpr import Swap
from sympy.sets.conditionset import conditionset
from axiom.discrete.combinatorics.factorial.adjacent import factorization, swapn
from sympy import Symbol


@plausible
def apply(given):
    assert given.is_ForAll
    S = given.rhs
    n = S.element_type.shape[0]
    
    k = Symbol.k(integer=True)
    x = given.variable
    
    w, i, j = given.function.lhs.args[0].args
    
    assert w[i, j].is_Swap or w[i, j].definition.is_Swap
    
    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True)
    
    P = Symbol.P(dtype=dtype.integer * n, definition=conditionset(p[:n], Equality(p[:n].set_comprehension(), Interval(0, n - 1, integer=True))))
    
    return ForAll[p[:n]:P, x:S](Contains(LAMBDA[k:n](x[p[k]]), S), given=given)


@check
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    S = Symbol.S(dtype=dtype.integer * n, given=True)    
    
    x = Symbol.x(shape=(oo,), integer=True)
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    
    w = Symbol.w(definition=LAMBDA[j:n, i:n](Swap(n, i, j)))
    
    given = ForAll[x[:n]:S](Contains(w[i, j] @ x[:n], S))
    
    Eq.P_definition, Eq.w_definition, Eq.swap, Eq.axiom = apply(given)
    
    Eq << factorization.apply(n)
    
    * _, b_i = Eq[-1].rhs.args[1].function.args
    b, _i = b_i.args
    Eq << Eq.w_definition.subs(j, b[_i]).subs(i, _i)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    k = Eq.axiom.lhs.variable
    Eq << Eq[-1][k]
    
    Eq << Eq[-1].this.function.function.rhs.args[0].limits_subs(_i, k)
    
    Eq << swapn.utility.apply(x[:n], b[:n], w)
    
    Eq << Eq[-1].subs(Eq[-2].reversed)
    
    Eq.axiom = Eq.axiom.subs(Eq[-1])
    
    Eq << swapn.mat_product.apply(Eq.swap.T, n, b)
    
    Eq << Eq.axiom.this.function.as_ForAll()


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
