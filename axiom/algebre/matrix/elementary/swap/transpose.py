from sympy.core.relational import Equality
from axiom.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Swap, Identity
from sympy.concrete.expr_with_limits import LAMBDA
from sympy import Symbol


@plausible
def apply(w):
    n = w.shape[0]
    i = w.generate_free_symbol(integer=True)
    j = w.generate_free_symbol({i}, integer=True)
    
    assert len(w.shape) == 4 and all(s == n for s in w.shape)
    assert w[i, j].is_Swap or w[i, j].definition.is_Swap 
    
    return Equality(w[i, j], w[j, i])


@check
def prove(Eq):
    n = Symbol.n(domain=Interval(2, oo, integer=True))
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    j = Symbol.j(domain=Interval(0, n - 1, integer=True))
    
    assert Identity(n).is_integer
    w = Symbol.w(integer=True, shape=(n, n, n, n), definition=LAMBDA[j, i](Swap(n, i, j)))
    
    Eq << apply(w)

    Eq << w[j, i].equality_defined()
    
    Eq << Eq[0] @ Eq[-1]
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.simplify(deep=True, wrt=Eq[-1].rhs.variable)
#     Eq << Eq[-1].this.rhs().function.args[-1].expr.simplify(deep=True, wrt=Eq[-1].rhs.variable)
    
    Eq << Eq[-1].this.rhs.function.as_KroneckerDelta()
    
    Eq << Eq[0] @ Eq[0]
    
    Eq << Eq[-1].subs(Eq[-2].reversed)
    
    Eq << w[i, j].inverse() @ Eq[-1]
    
    Eq << Eq[-1].forall((i,), (j,))


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
