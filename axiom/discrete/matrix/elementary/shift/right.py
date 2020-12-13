from sympy.core.relational import Equality
from axiom.utility import check, plausible

from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Shift
from sympy import LAMBDA
from sympy import Symbol


@plausible
def apply(x, w=None):
    n = x.shape[0]
    i = Symbol.i(domain=Interval(0, n - 1, integer=True))
    j = Symbol.j(domain=Interval(0, n - 1, integer=True))
    
    if w is None:
        w = Symbol.w(integer=True, shape=(n, n, n, n), definition=LAMBDA[j, i](Shift(n, i, j)))
    else:
        assert w[i, j] == Shift(n, i, j)
    
    return Equality(x @ w[i, j] @ w[i, j].T, x)


@check
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))    
    x = Symbol.x(shape=(n,), real=True)
    
    Eq << apply(x)
    
    i, j = Eq[0].lhs.indices    

    w = Eq[0].lhs.base
    
    Eq << (x @ w[i, j]).this.subs(Eq[0])
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs().function.args[1]().expr.simplify(wrt=Eq[-1].rhs.variable)
    
    Eq << (Eq[-1] @ w[i, j].T).this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.expand()    

    Eq << Eq[-1].this.rhs().function.args[1]().expr.simplify(wrt=Eq[-1].rhs.variable)
    
    Eq << Eq[-1].this.rhs().function.args[1]().expr.simplify()


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
