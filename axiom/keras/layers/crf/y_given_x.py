from axiom.utility import prove, apply
from sympy import *
from sympy.stats.rv import pspace
from sympy.stats.symbolic_probability import Probability as P
from axiom.keras.layers.crf.markov import assumptions, process_assumptions
from axiom import statistics, keras, algebra

import tensorflow as tf


@apply
def apply(*given):
    x, y = process_assumptions(*given)
    n, d = x.shape
    
    t = Symbol.t(domain=Interval(0, n - 1, integer=True))
    i = Symbol.i(integer=True)
    
    joint_probability = P(x[:t + 1], y[:t + 1])
    emission_probability = P(x[i] | y[i])
    transition_probability = P(y[i] | y[i - 1])
    y_given_x_probability = P(y | x)
    y = pspace(y).symbol
    
    G = Symbol.G(LAMBDA[y[i - 1], y[i]](-log(transition_probability)))    
    assert G.shape == (d, d)
    
    s = Symbol.s(LAMBDA[t](-log(joint_probability)))
    assert s.shape == (n,)
    
    x = Symbol.x(LAMBDA[y[i], i](-log(emission_probability)))
    assert x.shape == (n, d)
    
    z = Symbol.z(LAMBDA[y[t], t](Sum[y[:t]](E ** -s[t])))
    assert z.shape == (n, d)
    
    x_quote = Symbol.x_quote(-LAMBDA[t](log(z[t])))
    assert x_quote.shape == (n, d)
    
    return Equal(x_quote[t + 1], -log(ReducedSum(exp(-x_quote[t] - G))) + x[t + 1]), \
        Equal(-log(y_given_x_probability), tf.logsumexp(-x_quote[n - 1]) + s[n - 1])


@prove
def prove(Eq):
    Eq.s_definition, Eq.z_definition, Eq.x_quote_definition, Eq.x_definition, Eq.G_definition, *given, Eq.recursion, Eq.y_given_x = apply(*assumptions())
    x_probability = given[-1].lhs.arg.args[0]
    x = x_probability.lhs
    n = x.shape[0]
        
    s, t = Eq.s_definition.lhs.args
    Eq.z_definition = Eq.z_definition.apply(algebra.eq.imply.eq.lamda, (Eq.z_definition.lhs.indices[-1],), simplify=False)
    
    Eq << keras.layers.crf.markov.apply(*given)

    Eq << keras.layers.crf.logits.apply(Eq.G_definition.lhs.base, Eq.x_definition.lhs.base, s, Eq[-1])
    
    Eq << Eq.z_definition.subs(t, t + 1)
    
    Eq << Eq[-1].this.rhs.subs(Eq[-2])
    
    Eq << Eq[-1].this.rhs.function.simplify()

    Eq << Eq[-1].this.rhs.astype(Mul)
    
    Eq << Eq[-1].this.rhs.args[1].function.bisect(Slice[-1:])
    
    Eq << Eq[-1].this.rhs.args[1].function.astype(LAMBDA)
    
    Eq << Eq[-1].this.rhs.args[1].function.function.astype(Mul)
    
    Eq.z_recursion = Eq[-1].subs(Eq.z_definition.reversed)
    
    Eq << Eq.x_quote_definition.subs(t, t + 1)
    
    Eq << Eq[-1].this.rhs.subs(Eq.z_recursion)
    
    Eq << Eq[-1].this.rhs.args[1].astype(Add)
    
    Eq.z_definition_by_x_quote = E ** -Eq.x_quote_definition.reversed
    
    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)
    
    Eq << Eq[-1].this.rhs.args[1].args[1].arg.astype(exp)
    
    Eq.xy_joint_nonzero = statistics.is_nonzero.imply.is_nonzero.joint_slice.apply(given[-1], Slice[:t + 1, :t + 1])
    
    Eq << algebra.et.imply.cond.apply(statistics.is_nonzero.imply.et.apply(Eq.xy_joint_nonzero))
    
    y = Eq[-1].lhs.arg.lhs.base
    Eq << statistics.bayes.corollary.apply(Eq[-2], var=y[:t + 1])
    
    Eq << statistics.total_probability_theorem.apply(Eq[-1].lhs, y[:t + 1])
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq[-1].apply(algebra.eq.imply.ou.log)    
    
    Eq << algebra.et.imply.cond.apply(Eq[-1] & Eq.xy_joint_nonzero)
    
    Eq << Eq[-1].this.rhs.astype(Add)
    
    Eq << algebra.eq.imply.eq.exp.apply(-Eq.s_definition.reversed)
    
    Eq.y_given_x_log = Eq[-2].subs(Eq[-1])
    
    Eq << Eq.z_definition.apply(algebra.eq.imply.eq.reduced_sum)
    
    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)
    
    Eq << Eq.y_given_x_log.subs(Eq[-1].reversed) 
    
    Eq << Eq[-1].subs(t, n - 1)
    
    Eq << Eq.y_given_x.this.rhs.args[1].definition.reversed
    
    Eq << Eq[-1] + Eq[-2]


# reference: Neural Architectures for Named Entity Recognition.pdf
if __name__ == '__main__':
    prove()
