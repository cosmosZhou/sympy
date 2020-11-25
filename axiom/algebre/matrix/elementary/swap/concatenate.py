from sympy.core.relational import Equality
from axiom.utility import check, plausible
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Swap, Concatenate, ZeroMatrix
from sympy import Symbol


@plausible
def apply(n):
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)
    
    return Equality(Concatenate(Concatenate(Swap(n, i, j), ZeroMatrix(n)).T,
                                Concatenate(ZeroMatrix(n), 1)),
                    Swap(n + 1, i, j))


@check
def prove(Eq):
    n = Symbol.n(domain=[2, oo], integer=True)
    Eq << apply(n)

    _, i, j = Eq[0].rhs.args
    _i = i.copy(domain=[0, n - 1])
    _j = j.copy(domain=[0, n - 1])
    
    W = Symbol.W(definition=Eq[0].lhs._subs(i, _i)._subs(j, _j))
    V = Symbol.V(definition=Eq[0].rhs._subs(i, _i)._subs(j, _j))
    
    Eq << W.this.definition
    Eq << V.this.definition
    
    h = Symbol.h(integer=True, domain=[0, n])
    k = Symbol.k(integer=True, domain=[0, n])

    Eq << (V[h, k].this.definition, W[h, k].this.definition)

    Eq << (Eq[-1].this.rhs.as_KroneckerDelta(), Eq[-2].this.rhs.as_KroneckerDelta())
    
    Eq << Eq[-2] - Eq[-1] 
    
    Eq << Eq[-1].reference((k,), (h,))
    
    Eq << Eq[-1].subs(Eq[1]).subs(Eq[2])
    
    Eq << Eq[-1].forall((_i,), (_j,))
    
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
