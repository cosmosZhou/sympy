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
def apply(*given):
    forall_x, forall_p, equality = given
    assert forall_x.is_ForAll and forall_p.is_ForAll
    
    assert len(forall_x.limits) == 1
    x, S = forall_x.limits[0]
    
    assert forall_x.function.is_Equality
    x_set_comprehension, e = forall_x.function.args
    assert x_set_comprehension == x.set_comprehension()
    
    assert len(forall_p.limits) == 2
    (_x, _S), (p, P) = forall_p.limits
    assert x == _x and S == _S
    assert forall_p.function.is_Contains
    
    lamda, _S = forall_p.function.args
    assert S == _S
    assert lamda.is_LAMBDA
    
    n = x.shape[0]
    k = lamda.variable
    assert lamda == LAMBDA[k:n](x[p[k]])

    if P.is_set:    
        P = P.condition_set().condition
        
    assert p.shape[0] == n
    
    lhs, rhs = P.args
    assert rhs == Interval(0, n - 1, integer=True)    
    assert lhs == p.set_comprehension()
    
    assert equality.is_Equality
    
    assert equality.rhs == n
    assert equality.lhs.is_Abs
    assert equality.lhs.arg == e
     
    return Equality(abs(S), factorial(n), given=given)


@check
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    S = Symbol.S(etype=dtype.integer * n)    
    
    x = Symbol.x(**S.element_symbol().type.dict)
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    k = Symbol.k(integer=True)
    
    e = Symbol.e(etype=dtype.integer, given=True)
    
    p = Symbol.p(shape=(oo,), integer=True, nonnegative=True)
    
    P = Symbol.P(etype=dtype.integer * n, definition=conditionset(p[:n], Equality(p[:n].set_comprehension(), Interval(0, n - 1, integer=True))))

    Eq << apply(ForAll[x:S](Equality(x.set_comprehension(), e)),
                ForAll[x:S, p[:n]:P](Contains(LAMBDA[k:n](x[p[k]]), S)),
                Equality(abs(e), n))


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
