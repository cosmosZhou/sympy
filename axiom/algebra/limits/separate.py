from sympy.core.relational import Equal
from axiom.utility import prove, apply

from sympy import Symbol, Sum

import axiom

from sympy.core.numbers import oo
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(sgm):
    function, *limits = axiom.is_Sum(sgm)
    assert len(limits) > 1    
    limit, *limits = limits
    
    function = sgm.func(function, limit).simplify()
    
    return Equal(sgm, sgm.func(function, *limits))


@prove
def prove(Eq):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    n = Symbol.n(integer=True, positive=True)

    f = Symbol.f(shape=(oo,), real=True)
    g = Symbol.g(shape=(oo, oo), real=True)
     
    Eq << apply(Sum[i:0:n, j:0:n](f[j] * g[i, j]))
    
    Eq << Eq[-1].this.rhs.function.astype(Sum)


if __name__ == '__main__':
    prove()

