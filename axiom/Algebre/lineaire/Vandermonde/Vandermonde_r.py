from sympy.functions.combinatorial.factorials import binomial, factorial
from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import Ref, plausible, Product, identity, Sum
from sympy.core.relational import Equality
from sympy.matrices.expressions.determinant import Determinant

from sympy.matrices.expressions.matexpr import Shift
from axiom import discrete


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

    return Equality(Determinant([R, A]),
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
    r = Symbol('r')
    n = Symbol('n', domain=Interval(2, oo, integer=True))

    Eq << apply(r, n)

    (i, *iab), (j, *_) = Eq[0].lhs.arg.args[1].limits
#     i = i.copy(domain=Interval(*iab, integer=True))
    E = Ref[i:n, j]((-1) ** (j - i) * binomial(j + 1, i + 1))

    Eq << identity(Eq[0].lhs.arg @ E).expand()
    Eq << Eq[-1].this.rhs.args[1].function.simplifier()

    (k, *_), *_ = Eq[-1].rhs.args[1].function.limits

    _i = i.copy(domain=Interval(*iab, integer=True))
    Eq << discrete.combinatorics.stirling.second.definition.apply(_i + 1, j + 1)

    Eq << Eq[-1] * factorial(j + 1)
    Eq << Eq[-1].reversed

    Eq << Eq[-1].this.lhs.simplifier()

    Eq << Eq[-1].forall(_i)

    Eq << identity(Eq[2].rhs.args[1].function).limits_subs(k, k - 1)

    Eq << Eq[-1].subs(Eq[-2])
    
    Eq.equation = Eq[2].subs(Eq[-1])
    
    Eq << identity(Eq.equation.rhs.args[0].function).simplifier().limits_subs(k, k - 1)
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.args[1].simplifier()
    
    Eq << Eq[-1].subs(i, _i)
    
    Eq << discrete.combinatorics.binomial.theorem.apply(r, -1, _i + 1)
    
    Eq << Eq[-1].this.rhs.expand()
    
    Eq << Eq[-1].this.rhs.args[1].simplifier()
    
    Eq << Eq[-4] + (Eq[-1] - Eq[-1].lhs)
    
    Eq << Eq[-1].this.rhs.simplifier()
    
    Eq << discrete.combinatorics.binomial.theorem.apply(1, -1, _i + 1)
    
    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.rhs.simplifier()
    
    Eq << Eq[-4] + Eq[-1]
    
    Eq << Eq[-1].this.rhs.simplifier()
    
    Eq << identity(Sum[k:0:n - 1](Eq.equation.rhs.args[0].function.function._subs(i, _i))).simplifier()
    
    Eq << (Eq[-2].forall(_i), Eq[-1].forall(_i))
    
    Eq << Eq[-1].subs(Eq[-2]) 

    Eq << Eq.equation.subs(Eq[-1])
#     Eq << Eq.equation.this.rhs.subs(Eq[-1])

    Eq << Shift(n, 0, n - 1) @ Eq[-1]

    Eq << Eq[-1].det()

    Eq << Eq[-1].this.rhs.simplifier() 

    Eq << Eq[-1] * (-1) ** (n - 1) 

    Eq << Eq[-1].this.rhs.powsimp()

    Eq << Eq[-1].this.rhs.args[1].limits_subs(k, k - 1)

if __name__ == '__main__':
    prove(__file__)
