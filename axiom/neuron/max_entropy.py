# coding=utf-8
from sympy.core.symbol import Symbol
from sympy.utility import plausible
from sympy.core.relational import Equality
import sympy
from sympy import log, exp
from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import Ref
from sympy.concrete.summations import Sum
from sympy import var

@plausible
def apply(G, x, y):
    _, d = x.shape

    i = var(integer=True).i
    t = var(integer=True, nonnegative=True).t

    s = Symbol('s', shape=(oo,),
                    definition=Ref[t](Sum[i:1:t](G[y[i], y[i - 1]]) + Sum[i:0:t](x[i, y[i]])))

    z = Symbol('z', shape=(oo, d), definition=Ref[y[t], t](Sum[y[0:t]](sympy.E ** -s[t])))

    x_quote = Symbol("x'", shape=(oo, d),
                    definition=-Ref[t](sympy.log(z[t])))

    assert x_quote.is_real
    
    return Equality(x_quote[t + 1], -log(Sum(exp(-x_quote[t] - G))) + x[t + 1]), \
        Equality(-log(exp(-s[t]) / Sum[y[:t + 1]](exp(-s[t]))), log(Sum(exp(-x_quote[t]))) + s[t])


from sympy.utility import check


@check
def prove(Eq):
    d = var(integer=True).d
    G = Symbol('G', shape=(d, d), real=True)
    x = Symbol('x', shape=(oo, d), real=True)
    y = Symbol('y', shape=(oo,), integer=True)

    # n is the length of the sequence
    # d is the number of output labels

    Eq.s_definition, Eq.z_definition, Eq.x_quote_definition, Eq.recursion, Eq.entropy = apply(G, x, y)
    
    Eq.z_definition = Eq.z_definition.reference((Eq.z_definition.lhs.indices[-1],))
    
    t = Eq.recursion.lhs.indices[0] - 1
    s = Eq.s_definition.lhs.base 
    
    Eq << Eq.s_definition.subs(t, t + 1) - Eq.s_definition

    Eq << Eq[-1].this.rhs.simplify() + s[t]

    Eq << Eq.z_definition.subs(t, t + 1)
    
    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << Eq[-1].this.rhs.function.simplify()

    Eq << Eq[-1].this.rhs.as_two_terms()

    Eq << Eq[-1].this.rhs.args[1].function.bisect(back=1)

    Eq << Eq[-1].this.rhs.args[1].function.as_Ref()

    Eq << Eq[-1].this.rhs.args[1].function.function.as_two_terms()

    Eq << Eq[-1].this.rhs.subs(Eq.z_definition.reversed)

    Eq << Eq.x_quote_definition.subs(t, t + 1)

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << Eq[-1].this.rhs.args[1].as_Add()

    Eq.z_definition_by_x_quote = sympy.E ** -Eq.x_quote_definition.reversed

    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)

    Eq << Eq[-1].this.rhs.args[1].args[1].arg.simplify()

    Eq << Eq.entropy.this.lhs.args[1].as_Add()

    Eq << Eq[-1].exp().reversed

    Eq << Eq.z_definition.summation()

    Eq << Eq[-1].this.rhs.as_Sum()

    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)


# reference: Neural Architectures for Named Entity Recognition.pdf
if __name__ == '__main__':
    prove(__file__)
