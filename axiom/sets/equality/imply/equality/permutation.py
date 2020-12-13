from axiom.utility import plausible
from sympy.sets.contains import Subset, Supset
from sympy.core.relational import Equality
from sympy import Symbol
from axiom import discrete
from sympy.sets.sets import Interval
from sympy import UNION


@plausible
def apply(given, x):
    assert given.is_Equality
    p_set_comprehension, interval = given.args
    assert len(p_set_comprehension.limits) == 1
    i, zero, n_1 = p_set_comprehension.limits[0]
    assert zero.is_zero
    n = n_1 + 1
    assert p_set_comprehension.function.is_FiniteSet 
    p = p_set_comprehension.function.arg.base
    assert p_set_comprehension == p[:n].set_comprehension()
    zero, _n = interval.args
    assert zero.is_zero 
    assert _n == n and interval.right_open
    return Equality(UNION[i:n](x[p[i]].set), x[:n].set_comprehension())


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    p = Symbol.p(integer=True, shape=(n,))
    x = Symbol.x(integer=True, shape=(n,))
    
    Eq << apply(Equality(p.set_comprehension(), Interval(0, n - 1, integer=True)), x)

    A = Symbol.A(definition=Eq[1].lhs)
    B = Symbol.B(definition=Eq[1].rhs)
    Eq.A_definition = A.this.definition
    
    
    i = Eq[1].lhs.variable
    _i = Symbol.i(domain=Interval(0, n - 1, integer=True))    
    
    Eq.A_definition = Eq.A_definition.this.rhs.limits_subs(i, _i)
    j = Eq[1].rhs.variable
    _j = Symbol.j(domain=Interval(0, n - 1, integer=True))
    
    Eq.B_definition = B.this.definition
    Eq.B_definition = Eq.B_definition.this.rhs.limits_subs(Eq.B_definition.rhs.variable, _j)
    
    Eq.subset = Subset(Eq.A_definition.rhs, Eq.B_definition.rhs, plausible=True)    

    Eq << Eq.subset.simplify()
    
    Eq << Eq[-1].definition
    
    Eq << Eq[-1].subs(Eq[-1].variable, p[_i])    
    
    Eq.supset = Supset(Eq.subset.lhs, Eq.subset.rhs, plausible=True)    

    Eq << Eq.supset.simplify()
    
    Eq.definition = Eq[-1].definition    
    
    Eq << discrete.combinatorics.permutation.index.equality.apply(Eq[0], _j)
    
    index_j = Eq[-1].lhs.indices[0]
    Eq << Eq.definition.subs(Eq[-1].reversed)

    Eq << Eq[-1].subs(Eq[-1].variable, index_j)
    
    Eq <<= Eq.subset & Eq.supset
    
    Eq << Eq[-1].this.lhs.limits_subs(_i, i)
    
    Eq << Eq[-1].this.rhs.limits_subs(_j, j)

    
if __name__ == '__main__':
    prove(__file__)

