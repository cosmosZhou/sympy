
from axiom.utility import plausible
from sympy.core.relational import Equality

from sympy.functions.elementary.exponential import softmax, log, exp
from sympy import Symbol
from sympy.concrete.expr_with_limits import MAX
from sympy.concrete.summations import Sum
from axiom import neuron


# log softmax(x) = x - max(x) - log∑exp(x - max(x))
@plausible
def apply(x):
    assert len(x.shape) == 1

    return Equality(log(softmax(x)), x - MAX(x) - log(Sum(exp(x - MAX(x)))))


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, positive=True)
    
    x = Symbol.x(real=True, shape=(n,))
    Eq << apply(x)
    
    Eq << neuron.softmax.translation.apply(x, -MAX(x)).reversed
    
    Eq << Eq[-1].log()
    
    Eq << Eq[-1].this.rhs.arg.definition


if __name__ == '__main__':
    prove(__file__)
