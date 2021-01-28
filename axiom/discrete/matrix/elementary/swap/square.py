from sympy.core.relational import Equality
from axiom.utility import prove, apply
from sympy.sets.sets import Interval
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Swap, Identity
from sympy import LAMBDA
from sympy import Symbol
from axiom import algebre


@apply(imply=True)
def apply(w):
    n = w.shape[0]
    i = w.generate_free_symbol(integer=True)
    j = w.generate_free_symbol({i}, integer=True)
    
    assert len(w.shape) == 4 and all(s == n for s in w.shape)
    assert w[i, j].is_Swap or w[i, j].definition.is_Swap 
    
    return Equality(w[i, j] @ w[i, j], Identity(n))


@prove
def prove(Eq):
    n = Symbol.n(positive=True, integer=True)
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    
    assert Identity(n).is_integer
    w = Symbol.w(definition=LAMBDA[j, i](Swap(n, i, j)))
    
    Eq << apply(w)
    
    Eq << Eq[0] @ Eq[0]


if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
