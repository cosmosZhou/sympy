# coding=utf-8
from sympy import *
from axiom.utility import prove, apply
from sympy.stats.symbolic_probability import Probability as P
from sympy.stats.rv import pspace


@apply
def apply(G, x, s, given):
    t = s.definition.variable
    y = x.definition.variable.base
    return Equality(s[t + 1], G[y[t + 1], y[t]] + s[t] + x[t + 1, y[t + 1]])


@prove
def prove(Eq):
    # d is the number of output labels    
    # oo is the length of the sequence
    d = Symbol.d(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(shape=(n, d), real=True, random=True, given=True)
    y = Symbol.y(shape=(n,), domain=Interval(0, d - 1, integer=True), random=True, given=True)

    i = Symbol.i(integer=True)
    t = Symbol.t(integer=True, domain=[0, n])
    
    joint_probability_t = P(x[:t + 1], y[:t + 1])
    emission_probability = P(x[i] | y[i])
    transition_probability = P(y[i] | y[i - 1])
        
    given = Equality(joint_probability_t,
                    P(x[0] | y[0]) * P(y[0]) * Product[i:1:t + 1](transition_probability * emission_probability))
        
    y = pspace(y).symbol
    G = Symbol.G(shape=(d, d), definition=LAMBDA[y[i - 1], y[i]](-log(transition_probability)))
    s = Symbol.s(shape=(n,), definition=LAMBDA[t](-log(joint_probability_t)))
    x = Symbol.x(shape=(n, d), definition=LAMBDA[y[i], i](-log(emission_probability)))
    
    Eq.s_definition, Eq.G_definition, Eq.x_definition, Eq.given, Eq.logits_recursion = apply(G, x, s, given)

    Eq << Eq.s_definition.this.rhs.subs(Eq.given)
    
    Eq << Eq[-1].this.rhs.args[1].astype(Plus)
    
    Eq << Eq[-1].subs(Eq.x_definition.subs(i, 0).reversed)    
    
    Eq << Eq[-1].this.rhs.args[-1].args[1].astype(Sum)    
    
    Eq << Eq[-1].this.rhs.args[-1].args[1].function.astype(Plus)
    
    Eq << Eq[-1].this.rhs.args[-1].args[1].astype(Plus)
    
    Eq << Eq[-1].subs(Eq.x_definition.reversed).subs(Eq.G_definition.reversed)
    
    Eq << Eq[-1].this.rhs.args[-1].bisect({0})
    
    Eq << Eq[-1].subs(t, t + 1) - Eq[-1]
    
    s = Eq.s_definition.lhs.base    
    Eq << Eq[-1].this.rhs.simplify() + s[t]

    
# reference: Neural Architectures for Named Entity Recognition.pdf
if __name__ == '__main__':
    prove(__file__)
