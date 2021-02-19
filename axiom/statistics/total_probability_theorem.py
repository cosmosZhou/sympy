
from axiom.utility import prove, apply
from sympy.core.relational import Equality
from sympy.concrete.summations import Sum
from sympy.core.symbol import Symbol
from sympy.stats.rv import pspace
from sympy.integrals.integrals import Integral
from sympy.stats.symbolic_probability import Probability


@apply
def apply(self, given):
    marginal_probability = self.marginalize(given)
    x = pspace(given).symbol
    if given.is_integer:
        return Equality(Sum[x](self), marginal_probability)
    else:
        return Equality(Integral[x](self), marginal_probability)
        




@prove
def prove(Eq):
    x = Symbol.x(real=True, random=True)
    y = Symbol.y(real=True, random=True)
    P = Probability(x, y)
    Eq << apply(P, y)


if __name__ == '__main__':
    prove(__file__)
