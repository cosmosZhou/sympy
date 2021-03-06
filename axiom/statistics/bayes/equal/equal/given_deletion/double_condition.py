
from sympy.core.relational import Equality

from axiom.utility import prove, apply
from sympy import Symbol
from axiom.statistics import bayes
from sympy.stats.rv import pspace
from axiom import algebre, statistics


# given: x | y & z = x | y
# imply: x | z = x
@apply(imply=True)
def apply(*given):
    eq_x_given_yz, z_given_y = given
    assert z_given_y.is_Equality
    assert z_given_y.lhs.is_Conditioned
    z, y = z_given_y.lhs.args
    assert z == z_given_y.rhs
    
    assert eq_x_given_yz.is_Equality
    lhs, rhs = eq_x_given_yz.args
    assert lhs.is_Conditioned
    assert rhs.is_Conditioned
    
    x, yz = lhs.args
    _x, _y = rhs.args
    assert x == _x
    assert y == _y

    _y, _z = yz.args
    
    if _y != y:
        _z, _y = _y, _z    
    assert _z == z or _z == z.as_boolean()
    assert _y == y    
    
    return Equality(x | z, x)


@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    z = Symbol.z(real=True, random=True)
    
    Eq << apply(Equality(x | y.as_boolean() & z.as_boolean(), x | y), Equality(z | y, z))
    
    Eq.yz_nonzero, Eq.y_nonzero = Eq[0].domain_definition().split()
    
    _, Eq.z_nonzero = bayes.is_nonzero.et.apply(Eq.yz_nonzero).split()
    
    Eq << bayes.corollary.apply(Eq.yz_nonzero, var=x)
    
    Eq << Eq[-1].subs(Eq[0])
    
    Eq << bayes.corollary.apply(Eq.y_nonzero, var=z)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq.xy_probability = bayes.corollary.apply(Eq.y_nonzero, var=x)
    
    Eq << Eq[-1].subs(Eq.xy_probability.reversed)
    
    Eq << Eq[-1].subs(Eq[1])
    
    Eq << statistics.total_probability_theorem.apply(Eq[-1].lhs, y).subs(bayes.corollary.apply(Eq.z_nonzero, var=x))
    
    Eq << algebre.equal.imply.equal.integrate.apply(Eq[-2], (pspace(y).symbol,))
    
    Eq << Eq[-1].subs(Eq[-2])
    
    Eq << statistics.total_probability_theorem.apply(Eq.xy_probability.lhs, y)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << algebre.is_nonzero.equal.imply.equal.scalar.apply(Eq[-1], Eq.z_nonzero)


if __name__ == '__main__':
    prove(__file__)
