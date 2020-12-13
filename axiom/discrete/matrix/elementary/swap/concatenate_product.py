from sympy.core.relational import Equality
from axiom.utility import check, plausible
from sympy.core.numbers import oo

from sympy.matrices.expressions.matexpr import Swap, Concatenate, ZeroMatrix
from sympy import Symbol, Slice
from sympy.concrete.products import MatProduct
import axiom
from axiom import algebre


@plausible
def apply(n, m, b):
    i = Symbol.i(integer=True)    
    
    return Equality(Concatenate(Concatenate(MatProduct[i:m](Swap(n, i, b[i])), ZeroMatrix(n)).T,
                                Concatenate(ZeroMatrix(n), 1)).T,
                    MatProduct[i:m](Swap(n + 1, i, b[i])))


@check
def prove(Eq):
    n = Symbol.n(domain=[2, oo], integer=True)
    m = Symbol.m(domain=[1, oo], integer=True)
    b = Symbol.b(integer=True, shape=(oo,), nonnegative=True)
    
    Eq << apply(n, m, b)
    
    Eq.initial = Eq[0].subs(m, 1)
    
    Eq.concatenate = axiom.discrete.matrix.elementary.swap.concatenate.apply(n)
    
    * _, i, j = Eq.concatenate.rhs.args
    Eq << Eq.concatenate.subs(i, 0).subs(j, b[0]).T
    
    Eq.induction = Eq[0].subs(m, m + 1)
    
    Eq << Eq.induction.this.rhs.bisect(Slice[-1:])
    
    Eq << Eq[-1].subs(Eq[0].reversed)
    
    Eq << Eq.concatenate.subs(i, m).subs(j, b[m]).T
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq[-1].this.rhs.expand()
    
    i = Eq[0].rhs.variable
    Eq << Eq[-1].this.rhs.args[0].arg.args[0].limits_subs(i, i - 1)

    if Eq[0].equivalent is not None:
        Eq << Eq[0].induct(reverse=True)
    else:
        Eq << Eq.induction.induct()
    
    Eq << algebre.equality.sufficient.imply.equality.induction.apply(Eq.initial, Eq[-1], n=m, start=1)
    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
