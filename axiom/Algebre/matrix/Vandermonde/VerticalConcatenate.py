from sympy.functions.combinatorial.factorials import binomial, factorial
from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Equality
from sympy.matrices.expressions.determinant import Det

from sympy.matrices.expressions.matexpr import Shift
from axiom import discrete
from sympy.concrete.expr_with_limits import Ref
from sympy.concrete.products import Product
from sympy.concrete.summations import Sum


# r = Symbol('r')
# n = Symbol('n', integer=True, positive=True)
@plausible
def apply(r, n):
    if not n >= 2:
        return None
    k = Symbol('k', integer=True)
    i = Symbol('i', integer=True)
    j = Symbol('j', domain=Interval(0, n, right_open=True, integer=True))

    A = Ref[i:n - 1, j]((j + 1) ** (i + 1))
    R = Ref[j](1 - r ** (j + 1))
# note : [A, B].T = (A.T, B.T)
# [R, A] = (R.T, A.T).T

    return Equality(Det([R, A]),
                    (1 - r) ** n * Product[k:1:n - 1](factorial(k)))


from sympy.utility import check


def numeric_prove():
    import numpy as np
    from scipy.special.basic import comb
    n = 8
    E = np.eye(n, dtype=int)
    print(E)

    for k in range(n):
        for j in range(n - 1, k - 1, -1):
            if j > 0:
                E[:, j] -= E[:, j - 1]

    print(E)
    _E = np.zeros((n, n), dtype=int)
    for i in range(n):
        for j in range(n):
            _E[i][j] = (-1) ** (j - i) * comb(j + 1, i + 1)

    print(_E)

    assert (_E == E).all()

    A = np.zeros((n - 1, n), dtype=int)
    for i in range(n - 1):
        for j in range(n):
            A[i][j] = (j + 1) ** (i + 1)

    print(A)
    A_ = A @ E
    print(A_)


@check
def prove(Eq):
    r = Symbol('r', real=True)
    n = Symbol('n', domain=Interval(2, oo, integer=True))    

    Eq << apply(r, n)

    (i, *iab), (j, *_) = Eq[0].lhs.arg.args[1].limits
    
    assert (2*i).is_even
    
    E = Ref[i:n, j]((-1) ** (j - i) * binomial(j + 1, i + 1))

    Eq << (Eq[0].lhs.arg @ E).this.expand()

    (k, *_), *_ = Eq[-1].rhs.args[1].function.limits

    _i = i.copy(domain=Interval(*iab, integer=True))
    Eq << discrete.combinatorics.stirling.second.definition.apply(_i + 1, j + 1)

    Eq << Eq[-1] * factorial(j + 1)
    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].forall(_i)

    Eq << Eq[1].rhs.args[1].function.this.limits_subs(k, k - 1)

    Eq << Eq[-1].subs(Eq[-2])
    
    Eq.equation = Eq[1].subs(Eq[-1])
    
    Eq << Eq.equation.rhs.args[0].function.this.limits_subs(j, j - 1)
    
    _j = Eq[-1].rhs.variable
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.args[1].simplify()
    
    Eq << Eq[-1].subs(i, _i)
    
    Eq << Eq[-1].this.lhs.limits_subs(j, _j)
    
    Eq << discrete.combinatorics.binomial.theorem.apply(r, -1, _i + 1, _j)
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.args[1].simplify()
    
    Eq << Eq[-4] + (Eq[-1] - Eq[-1].lhs)
    
    Eq << Eq[-1].this.rhs.simplify()
    
    Eq << discrete.combinatorics.binomial.theorem.apply(1, -1, _i + 1, _j)
    
    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.simplify()
    
    Eq << Eq[-4] + Eq[-1]
    
    Eq << Eq[-1].this.rhs.simplify()
    
    Eq << Sum[j](Eq.equation.rhs.args[0].function.function._subs(i, _i)).this.limits_subs(j, _j)
    
    Eq << (Eq[-2].forall(_i), Eq[-1].forall(_i))
    
    Eq << Eq[-1].subs(Eq[-2]) 

    Eq << Eq.equation.subs(Eq[-1])

    Eq << Shift(n, 0, n - 1) @ Eq[-1]

    Eq << Eq[-1].det()

    Eq << Eq[-1].this.rhs.simplify() 

    Eq << Eq[-1] * (-1) ** (n - 1) 

    Eq << Eq[-1].this.rhs.powsimp()

    var = Eq[-1].rhs.args[1].variable
    Eq << Eq[-1].this.rhs.args[1].limits_subs(var, var - 1)

if __name__ == '__main__':
    prove(__file__)
