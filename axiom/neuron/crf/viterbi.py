from sympy import Symbol, Slice
from axiom.utility import plausible
from sympy.core.relational import Equality

from sympy import LAMBDA, MIN, MAX, Minimize
import sympy
from sympy.functions.elementary.exponential import log, exp
from sympy.stats.symbolic_probability import Probability as P
from sympy.stats.rv import pspace
from axiom.neuron.crf.markov import process_assumptions, assumptions
from sympy.sets.sets import Interval
from axiom import neuron


@plausible
def apply(*given):
    x, y = process_assumptions(*given)

    n, d = x.shape
    t = Symbol.t(domain=Interval(0, n - 1, integer=True))
    i = Symbol.i(integer=True)
    
    joint_probability_t = P(x[:t + 1], y[:t + 1])
    joint_probability = P(x, y)
    emission_probability = P(x[i] | y[i])
    transition_probability = P(y[i] | y[i - 1])
    y = pspace(y).symbol
    
    G = Symbol.G(definition=LAMBDA[y[i - 1], y[i]](-sympy.log(transition_probability)))
    assert G.shape == (d, d)
    s = Symbol.s(definition=LAMBDA[t](-log(joint_probability_t)))
    assert s.shape == (n,)
    x = Symbol.x(definition=LAMBDA[y[i], i](-sympy.log(emission_probability)))
    assert x.shape == (n, d)
    x_quote = Symbol.x_quote(definition=LAMBDA[y[t], t](MIN[y[:t]](s[t])))
    assert x_quote.shape == (n, d)

    assert x_quote.is_real
    return Equality(x_quote[t + 1], x[t + 1] + MIN(x_quote[t] + G)), \
        Equality(MAX[y](joint_probability), exp(-MIN(x_quote[n - 1])))


from axiom.utility import check


@check
def prove(Eq):
    Eq.s_definition, Eq.x_quote_definition, Eq.x_definition, Eq.G_definition, *given, Eq.recursion, Eq.joint_probability = apply(*assumptions())
    
    x_probability = given[-1].lhs.arg.args[0]
    x = x_probability.lhs
    n = x.shape[0]
    
    s, t = Eq.s_definition.lhs.args
    Eq.x_quote_definition = Eq.x_quote_definition.reference((Eq.x_quote_definition.lhs.indices[-1],))
    
    Eq << neuron.crf.markov.apply(*given)
    
    Eq << neuron.crf.logits.apply(Eq.G_definition.lhs.base, Eq.x_definition.lhs.base, s, Eq[-1])
    
    Eq << Eq.x_quote_definition.subs(t, t + 1)
    y = Eq[-1].rhs.variable.base

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << Eq[-1].this.rhs.function.simplify()
    
    Eq << Eq[-1].this.rhs.args[1].function.bisect(Slice[-1:])
    
    Eq << Eq[-1].this.rhs.args[1].function.astype(LAMBDA)
    
    Eq << Eq[-1].this.rhs.args[1].astype(Minimize)
    
    Eq << Eq[-1].subs(Eq.x_quote_definition.reversed)
    
    Eq << -Eq.s_definition.reversed
    
    Eq << Eq[-1].exp()
 
    Eq << Eq[-1].max((y[:t + 1],))
    
    Eq << Eq[-1].this.rhs.astype(exp)
    
    Eq << Eq.x_quote_definition.min().this.rhs.simplify(wrt=t)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq[-1].subs(t, n - 1)


if __name__ == '__main__':
    prove(__file__)
