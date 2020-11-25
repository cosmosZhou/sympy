
from axiom.utility import plausible
from sympy.core.relational import Equality

from sympy.functions.elementary.exponential import softmax, log, exp
from sympy import Symbol
from sympy.concrete.expr_with_limits import MAX
from sympy.concrete.summations import Sum
from sympy.core.mul import Times


# log softmax(x) = x - max(x) - log∑exp(x - max(x))
@plausible
def apply(x, delta):
    assert len(x.shape) == 1
    assert not delta.shape

    return Equality(softmax(x + delta), softmax(x))


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    
    x = Symbol.x(real=True, shape=(n,))
    delta = Symbol.delta(real=True)
    Eq << apply(x, delta)
    
    Eq << Eq[-1].this.lhs.definition
    
    Eq << Eq[-1].this.lhs.args[-1].args[0].function.astype(Times)
    
    Eq << Eq[-1].this.lhs.powsimp()
    
    Eq << Eq[-1].this.rhs.definition


if __name__ == '__main__':
    prove(__file__)
