# coding=utf-8
from axiom.utility import prove, apply
from sympy import *
from sympy.stats.rv import pspace
from sympy.stats.symbolic_probability import Probability as P
from axiom.keras.layers.crf.markov import assumptions, process_assumptions
from axiom.statistics import bayes
from axiom import statistics, keras, algebre

import tensorflow as tf


@apply(imply=True)
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
    
    G = Symbol.G(definition=LAMBDA[y[i - 1], y[i]](-log(transition_probability)))    
    assert G.shape == (d, d)
    
    s = Symbol.s(definition=LAMBDA[t](-log(joint_probability)))
    assert s.shape == (n,)
    
    x = Symbol.x(definition=LAMBDA[y[i], i](-log(emission_probability)))
    assert x.shape == (n, d)
    
    z = Symbol.z(definition=LAMBDA[y[t], t](Sum[y[:t]](E ** -s[t])))
    assert z.shape == (n, d)
    
    x_quote = Symbol.x_quote(definition=-LAMBDA[t](log(z[t])))
    assert x_quote.shape == (n, d)
    
    return Equality(x_quote[t + 1], -log(ReducedSum(exp(-x_quote[t] - G))) + x[t + 1]), \
        Equality(-log(y_given_x_probability), tf.logsumexp(-x_quote[n - 1]) + s[n - 1])


@prove
def prove(Eq):
    Eq.s_definition, Eq.z_definition, Eq.x_quote_definition, Eq.x_definition, Eq.G_definition, *given, Eq.recursion, Eq.y_given_x = apply(*assumptions())
    x_probability = given[-1].lhs.arg.args[0]
    x = x_probability.lhs
    n = x.shape[0]
        
    s, t = Eq.s_definition.lhs.args
    Eq.z_definition = Eq.z_definition.apply(algebre.equal.imply.equal.lamda, (Eq.z_definition.lhs.indices[-1],), simplify=False)
    
    Eq << keras.layers.crf.markov.apply(*given)

    Eq << keras.layers.crf.logits.apply(Eq.G_definition.lhs.base, Eq.x_definition.lhs.base, s, Eq[-1])
    
    Eq << Eq.z_definition.subs(t, t + 1)
    
    Eq << Eq[-1].this.rhs.subs(Eq[-2])
    
    Eq << Eq[-1].this.rhs.function.simplify()

    Eq << Eq[-1].this.rhs.astype(Times)
    
    Eq << Eq[-1].this.rhs.args[1].function.bisect(Slice[-1:])
    
    Eq << Eq[-1].this.rhs.args[1].function.astype(LAMBDA)
    
    Eq << Eq[-1].this.rhs.args[1].function.function.astype(Times)
    
    Eq.z_recursion = Eq[-1].subs(Eq.z_definition.reversed)
    
    Eq << Eq.x_quote_definition.subs(t, t + 1)
    
    Eq << Eq[-1].this.rhs.subs(Eq.z_recursion)
    
    Eq << Eq[-1].this.rhs.args[1].astype(Plus)
    
    Eq.z_definition_by_x_quote = E ** -Eq.x_quote_definition.reversed
    
    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)
    
    Eq << Eq[-1].this.rhs.args[1].args[1].arg.astype(exp)
    
    Eq.xy_joint_nonzero = bayes.is_nonzero.is_nonzero.joint_slice.apply(given[-1], Slice[:t + 1, :t + 1])
    
    Eq << bayes.is_nonzero.et.apply(Eq.xy_joint_nonzero).split()
    
    y = Eq[-1].lhs.arg.lhs.base
    Eq << bayes.corollary.apply(Eq[-2], var=y[:t + 1])
    
    Eq << statistics.total_probability_theorem.apply(Eq[-1].lhs, y[:t + 1])
    
    Eq << Eq[-2].subs(Eq[-1].reversed)
    
    Eq << Eq[-1].apply(algebre.equal.imply.ou.log)    
    
    Eq << (Eq[-1] & Eq.xy_joint_nonzero).split()
    
    Eq << Eq[-1].this.rhs.astype(Plus)
    
    Eq << algebre.equal.imply.equal.exp.apply(-Eq.s_definition.reversed)
    
    Eq.y_given_x_log = Eq[-2].subs(Eq[-1])
    
    Eq << Eq.z_definition.apply(algebre.equal.imply.equal.sum)
    
    Eq << Eq[-1].this.rhs.simplify(wrt=t)
    
    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)
    
    Eq << Eq.y_given_x_log.subs(Eq[-1].reversed) 
    
    Eq << Eq[-1].subs(t, n - 1)
    
    Eq << Eq.y_given_x.this.rhs.args[1].definition.reversed
    
    Eq << Eq[-1] + Eq[-2]


# reference: Neural Architectures for Named Entity Recognition.pdf
if __name__ == '__main__':
    prove(__file__)
