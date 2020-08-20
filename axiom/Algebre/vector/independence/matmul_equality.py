from sympy.core.symbol import Symbol
from sympy.sets.sets import Interval
from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Equality
from sympy.concrete.expr_with_limits import Ref

@plausible
def apply(given):
    assert given.is_Equality
    lhs, rhs = given.args        
    
    assert lhs.is_MatMul
    p_polynomial, x = lhs.args
    
    assert rhs.is_MatMul
    _p_polynomial, y = rhs.args
    
    assert p_polynomial == _p_polynomial
    
    assert p_polynomial.is_Ref
    assert p_polynomial.shape == x.shape == y.shape    
    assert len(p_polynomial.shape) == 1
#     n = p_polynomial.shape[0]
    k = p_polynomial.variable
    polynomial = p_polynomial.function
    assert polynomial.is_Power
    
    b, e = polynomial.as_base_exp()    
    assert not b.has(k)
    assert e.as_poly(k).degree() == 1
    
    return Equality(x, y, given=given)


from sympy.utility import check


@check
def prove(Eq):
    p = Symbol("p", complex=True)    
    n = Symbol('n', domain=Interval(1, oo, integer=True))
    x = Symbol("x", shape=(n,), complex=True, given=True)
    y = Symbol("y", shape=(n,), complex=True, given=True)
    k = Symbol('k', domain=Interval(1, oo, integer=True))
    
    assert x.is_given and y.is_given
    
    given = Equality(Ref[k:n](p ** k) @ x, Ref[k:n](p ** k) @ y)
    
    Eq << apply(given)
    
    i = Symbol('i', domain=Interval(1, n, integer=True))
    Eq << given.subs(p, i)
    
    Eq << Eq[-1].forall(i)
    
    Eq << Eq[-1].as_Equal()


if __name__ == '__main__':
    prove(__file__)
