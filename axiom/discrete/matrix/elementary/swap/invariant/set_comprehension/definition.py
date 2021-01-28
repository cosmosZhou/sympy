from sympy.core.relational import Equality

from axiom.utility import prove, apply

from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Swap
from sympy import LAMBDA
from sympy import Symbol
import axiom
from axiom import algebre, discrete


@apply(imply=True)
def apply(a, free_symbol=None):
    matmul = axiom.is_definition(a)
    lhs, rhs = axiom.is_MatMul(matmul)
    
    if lhs.is_Swap:
        w = lhs
        x = rhs
    elif rhs.is_Swap:
        w = rhs
        x = lhs
    else:
        return
 
    return Equality(a.set_comprehension(free_symbol=free_symbol), x.set_comprehension(free_symbol=free_symbol).simplify())


@prove
def prove(Eq): 
    n = Symbol.n(domain=Interval(2, oo, integer=True))    
    x = Symbol.x(shape=(n,), integer=True)    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    k = Symbol.k(integer=True)
    a = Symbol.a(definition=x @ Swap(n, i, j))
    Eq << apply(a, free_symbol=k)
    
    w = Symbol.w(definition=LAMBDA[j, i](Swap(n, i, j)))
    
    Eq << w[i, j].this.definition
    
    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << discrete.matrix.elementary.swap.invariant.set_comprehension.union_comprehension.apply(x, w, right=True, free_symbol=k)
    
    Eq << Eq[-2][k]
    
    Eq << Eq[-2].subs(Eq[-1].reversed)

    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
