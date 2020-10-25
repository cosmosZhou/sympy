# coding=utf-8
from axiom.utility import plausible
from sympy.core.relational import Equality
import sympy
from sympy import log
from sympy.concrete.expr_with_limits import LAMBDA
from sympy import Symbol
from sympy.concrete.products import Product
from sympy.stats.symbolic_probability import Probability as P
from sympy.stats.rv import pspace


@plausible
def apply(G, x, s, given):
    t = s.definition.variable
    y = x.definition.variable.base
    return Equality(s[t + 1], G[y[t + 1], y[t]] + s[t] + x[t + 1, y[t + 1]], given=given)


from axiom.utility import check


@check
def prove(Eq):
    # d is the number of output labels    
    # oo is the length of the sequence
    d = Symbol.d(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(shape=(n, d), real=True, random=True, given=True)
    y = Symbol.y(shape=(n,), integer=True, domain=[0, d - 1], random=True, given=True)

    i = Symbol.i(integer=True)
    t = Symbol.t(integer=True, domain=[0, n])
    
    joint_probability_t = P(x[:t + 1], y[:t + 1])
    emission_probability = P(x[i] | y[i])
    transition_probability = P(y[i] | y[i - 1])
        
    given = Equality(joint_probability_t,
                    P(x[0] | y[0]) * P(y[0]) * Product[i:1:t](transition_probability * emission_probability))
        
    y = pspace(y).symbol
    G = Symbol.G(shape=(d, d), definition=LAMBDA[y[i - 1], y[i]](-sympy.log(transition_probability)))
    s = Symbol.s(shape=(n,), definition=LAMBDA[t](-log(joint_probability_t)))
    x = Symbol.x(shape=(n, d), definition=LAMBDA[y[i], i](-sympy.log(emission_probability)))
    
    Eq.s_definition, Eq.G_definition, Eq.x_definition, Eq.given, Eq.logits_recursion = apply(G, x, s, given=given)

    Eq << Eq.s_definition.subs(Eq.given)
    
    Eq << Eq[-1].this.rhs.args[1].as_Add()
    
    Eq << Eq[-1].subs(Eq.x_definition.subs(i, 0).reversed)    
    
    Eq << Eq[-1].this.rhs.args[-1].args[1].as_Add()    
    
    Eq << Eq[-1].this.rhs.args[-1].args[1].function.as_Add()
    
    Eq << Eq[-1].this.rhs.args[-1].args[1].as_two_terms()
    
    Eq << Eq[-1].subs(Eq.x_definition.reversed).subs(Eq.G_definition.reversed)
    
    Eq << Eq[-1].this.rhs.args[-1].bisect({0})
    
    Eq << Eq[-1].subs(t, t + 1) - Eq[-1]
    
    s = Eq.s_definition.lhs.base    
    Eq << Eq[-1].this.rhs.simplify() + s[t]

    
# reference: Neural Architectures for Named Entity Recognition.pdf
if __name__ == '__main__':
    prove(__file__)
