from sympy import Symbol, Slice
from axiom.utility import plausible
from sympy.core.relational import Equality

from sympy.concrete.expr_with_limits import LAMBDA, MIN, MAX
import sympy
from sympy.functions.elementary.exponential import log, exp
from sympy.stats.symbolic_probability import Probability as P
from sympy.stats.rv import pspace
from axiom.neuron import crf
from axiom.neuron.crf.markov import process_assumptions, assumptions
from sympy.functions.elementary.piecewise import Piecewise


@plausible
def apply(*given):
    x, y = process_assumptions(*given)

    n, d = x.shape
    t = Symbol.t(integer=True, domain=[0, n - 1])
    i = Symbol.i(integer=True)
    
    joint_probability_t = P(x[:t + 1], y[:t + 1])
    joint_probability = P(x, y)
    emission_probability = P(x[i] | y[i])
    transition_probability = P(y[i] | y[i - 1])
    y = pspace(y).symbol
    
    G = Symbol.G(shape=(d, d), definition=LAMBDA[y[i - 1], y[i]](-sympy.log(transition_probability)))
    s = Symbol.s(shape=(n,), definition=LAMBDA[t](-log(joint_probability_t)))
    x = Symbol.x(shape=(n, d), definition=LAMBDA[y[i], i](-sympy.log(emission_probability)))

    x_quote = Symbol.x_quote(shape=(n, d), definition=LAMBDA[y[t], t](Piecewise((MIN[y[0:t]](s[t]), t > 0),
                                                                     (s[0], True))))

    assert x_quote.is_real
    return Equality(x_quote[t + 1], x[t + 1] + MIN(x_quote[t] + G), given=given), \
        Equality(MAX[y](joint_probability), exp(-MIN(x_quote[n - 1])), given=given)


from axiom.utility import check


@check
def prove(Eq):
    Eq.s_definition, Eq.x_quote_definition, Eq.x_definition, Eq.G_definition, *given, Eq.recursion, Eq.joint_probability = apply(*assumptions())
    
    x_probability = given[-1].lhs.arg.args[0]
    x = x_probability.lhs
    n = x.shape[0]
    
    s, t = Eq.s_definition.lhs.args
    Eq << Eq.x_quote_definition.reference((Eq.x_quote_definition.lhs.indices[-1],))
    
    Eq.x_quote_definition = Eq[-1].this.rhs.as_Piecewise()
    
    Eq.x_quote_definition_1 = Eq.x_quote_definition.forall((t, 1, n - 1))
    Eq.x_quote_definition_0 = Eq.x_quote_definition.subs(t, 0)
    
    Eq << crf.markov.apply(*given)
    
    Eq << crf.logits.apply(Eq.G_definition.lhs.base, Eq.x_definition.lhs.base, s, Eq[-1])
    
    Eq << Eq.x_quote_definition.subs(t, t + 1)
    y = Eq[-1].rhs.variable.base

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << Eq[-1].this.rhs.function.simplify()
    
    Eq.bisect0, Eq.bisect1 = Eq[-1].bisect(t > 0).split()    
    
    Eq << Eq.bisect1.this().function.rhs.args[1].function.bisect(Slice[-1:])
    
    Eq << Eq[-1].this.function.rhs.args[1].function.as_Ref()
    
    Eq << Eq[-1].this.function.rhs.args[1].as_Min()
    
    Eq.x_quote_recursion = Eq[-1].subs(Eq.x_quote_definition_1.reversed)
    
    Eq << Eq.bisect0.this.rhs.args[1].function.as_Ref()
    Eq << Eq[-1].this.rhs.args[1].as_Min()
    Eq << Eq[-1].subs(Eq.x_quote_definition_0.reversed)
    
    Eq <<= Eq.x_quote_recursion & Eq[-1]
    
    Eq << Eq[-1].subs(Eq.x_quote_recursion.variable, t)
    
    Eq << -Eq.s_definition.reversed
    
    Eq << Eq[-1].exp()
 
    Eq << Eq[-1].max((y[:t + 1],))
    
    Eq << Eq[-1].this.rhs.as_Exp()
    
    Eq << Eq.x_quote_definition.min().this.rhs.simplify(wrt=t)
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq[-1].subs(t, n - 1)


if __name__ == '__main__':
    prove(__file__)
