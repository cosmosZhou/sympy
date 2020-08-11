from sympy.core.numbers import oo
from sympy.utility import plausible
from sympy.core.relational import Equality
from sympy import sqrt, pi, exp, Symbol
from sympy.integrals.integrals import Integral


@plausible
def apply():
    x = Symbol("x", real=True)
    return Equality(1 / sqrt(2 * pi) * Integral(exp(-x * x / 2), (x, -oo, oo)), 1, evaluate=False)


from sympy.utility import check


@check
def prove(Eq):
    Eq << apply()
    
    assert Eq[-1].lhs.is_extended_real
    Eq << Eq[0] * sqrt(2 * pi)

    x, *_ = Eq[-1].this.lhs.limits[0]
    y = Symbol("y", real=True)

    assert Eq[-1].lhs.is_extended_real    
    Eq << Eq[-1].this.lhs.limits_subs(x, y) * Eq[-1]

    assert Eq[-1].lhs.is_extended_real
    Eq << Eq[-1].this.lhs.as_multiple_limits()

    assert Eq[-1].lhs.is_extended_real
    Eq << Eq[-1].this.lhs.as_polar_coordinate()
    
    assert Eq[-1].lhs.is_extended_real
    Eq << Eq[-1].this.lhs.doit()
    
    assert Eq[-1].lhs.is_extended_real
    Eq << Eq[-3].this.lhs.args[1].limits_subs(y, x)
    
    assert Eq[-1].lhs.is_extended_real
    Eq << Eq[-1].sqrt()


# https://ccjou.wordpress.com/2012/11/26/jacobian-矩陣與行列式/
if __name__ == '__main__':
    prove(__file__)
