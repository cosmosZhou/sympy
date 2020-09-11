from sympy.core.relational import Equality
from sympy.core.symbol import dtype
from sympy.utility import check, plausible
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import ForAll, Ref, Exists
from sympy.matrices.expressions.matexpr import Swap
from sympy.sets.conditionset import conditionset
from sympy.concrete.products import MatProduct
from sympy import var
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.matrices import Matrix

@plausible
def apply(n):
    i = var(integer=True).i
    
    p = var(shape=(oo,), integer=True, nonnegative=True).p
    
    P = var(dtype=dtype.integer * n, definition=conditionset(p[:n], Equality(p[:n].set_comprehension(), Interval(0, n - 1, integer=True)))).P
    
    b = var(integer=True, shape=(oo,), nonnegative=True).b
    
    return ForAll[p[:n]:P](Exists[b[:n]](Equality(p[:n], Ref[i:n](i) @ MatProduct[i:n](Swap(n, i, b[i])))))


@check
def prove(Eq): 
    n = var(domain=[2, oo], integer=True).n
    
    Eq << apply(n)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << Eq[-1].subs(n, 2)
    
    Eq << Eq[-1].doit()
    
#     b[0] = 0, b[1] = KroneckerDelta[p[0], 0]
    b = Eq[-2].function.variable
    p = Eq[-1].variable
    Eq << Eq[-1].subs(b, Matrix((0, KroneckerDelta(p[0], 0))))
    
    Eq << Eq[-1].this.function.rhs.expand()
    
    

    
if __name__ == '__main__':
    prove(__file__)
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
