from sympy.core.symbol import Symbol
from sympy.utility import Ref, Sum, plausible
from sympy.core.relational import Equality
from sympy.tensor.indexed import IndexedBase
import sympy
from sympy import log, exp
from sympy.core.numbers import oo


@plausible
def apply(G, x, y):
    _, d = x.shape

    i = Symbol('i', integer=True)
    t = Symbol('t', integer=True, nonnegative=True)

    s = IndexedBase('s', (oo,),
                    definition=Ref[t](Sum[i:1:t](G[y[i], y[i - 1]]) + Sum[i:0:t](x[i, y[i]])))

    z = IndexedBase('z', shape=(oo, d),
                    definition=Ref[t](Ref[y[t]](Sum[y[0:t]](sympy.E ** -s[t]))))

    x_quote = IndexedBase("x'", shape=(oo, d),
                    definition=-Ref[t](sympy.log(z[t])))

    return Equality(x_quote[t + 1], -log(Sum(exp(-x_quote[t] - G))) + x[t + 1]), \
        Equality(-log(exp(-s[t]) / Sum[y[:t + 1]](exp(-s[t]))), log(Sum(exp(-x_quote[t]))) + s[t])


from sympy.utility import check


@check
def prove(Eq):
    d = Symbol('d', integer=True)
    G = IndexedBase('G', (d, d))
    x = IndexedBase('x', (oo, d))
    y = IndexedBase('y', (oo,), integer=True)

    # n is the length of the sequence
    # d is the number of output labels

    Eq.s_definition, Eq.z_definition, Eq.x_quote_definition, Eq.plausible0, Eq.plausible1 = apply(G, x, y)
    
    t = Eq.plausible0.lhs.indices[0] - 1
    x_quote = Eq.plausible0.lhs.base

    z = x_quote.definition.args[1].function.arg.base
    s = z.definition.function.function.function.arg.args[1].base
    
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

    Eq << Eq.plausible1.this.lhs.args[1].as_Add()

    Eq << Eq[-1].exp().reversed

    Eq << Eq.z_definition.summation()

    Eq << Eq[-1].this.rhs.as_Sum()

    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)


# reference: Neural Architectures for Named Entity Recognition.pdf
if __name__ == '__main__':
    prove(__file__)
