
from sympy.core.relational import Equal
from axiom.utility import prove, apply
from sympy import Symbol
from sympy.stats.drv_types import DieDistribution
from sympy.stats.symbolic_probability import Expectation
from sympy.functions.elementary.integers import floor


@apply
def apply(n):
    X = Symbol.X(integer=True, random=True)
    if n.is_even:
        return Equal(Expectation[X:DieDistribution(n)](X | (X > n / 2)), (3 * n + 2) / 4)
    elif n.is_odd:
        return Equal(Expectation[X:DieDistribution(n)](X | (X > n / 2)), (3 * n + 1) / 4)
    else:
        return Equal(Expectation[X:DieDistribution(n)](X | (X > n / 2)), n / 2 + floor(n / 2) / 2)


@prove
def prove(Eq):    
    n = Symbol.n(integer=True, positive=True)
    if n.is_even:
        assert (n + 1).is_odd
        assert (n / 2).is_integer
        assert n >= 2
        assert n / 2 >= 1
        assert not ((n + 1) / 2).is_integer
    elif n.is_odd:
        assert (n + 1).is_even
        assert ((n + 1) / 2).is_integer
        assert n >= 1
        assert not (n / 2).is_integer
        
    Eq << apply(n)
    
    Eq << Eq[-1].this.lhs.doit()
        
    Eq << Eq[-1].this.lhs.ratsimp()


if __name__ == '__main__':
    prove()
