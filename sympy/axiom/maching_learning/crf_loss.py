from sympy.core.symbol import Symbol
from sympy.utility import Ref, Sum, Eq, Min, plausible
from sympy.core.relational import Equality
from sympy.tensor.indexed import IndexedBase
import sympy
from sympy import log, exp


def apply(G, x, y):
    n, d = x.shape

    i = Symbol('i', integer=True)

    t = Symbol('t', integer=True)

    s = IndexedBase('s', (n,),
                    definition=Ref[t](Sum[i:1:t](G[y[i], y[i - 1]]) + Sum[i:0:t](x[i, y[i]])))

    z = IndexedBase('z', shape=(n, d),
                    definition=Ref[t](Ref[y[t]](Sum[y[0:t]](sympy.E ** -s[t]))))

    x_quote = IndexedBase("x'", shape=(n, d),
                    definition=-Ref[t](sympy.log(z[t])))

    return Equality(x_quote[t + 1], -log(Sum(exp(-x_quote[t] - G))) + x[t + 1], plausible=plausible()), \
        Equality(-log(exp(-s[n - 1]) / Sum[y](exp(-s[n - 1]))), log(Sum(exp(-x_quote[n - 1]))) + s[n - 1], plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    n = Symbol('n', integer=True)
    d = Symbol('d', integer=True)
    G = IndexedBase('G', (d, d))
    x = IndexedBase('x', (n, d))
    y = IndexedBase('y', (n,))

    # n is the length of the sequence
    # d is the number of output labels

    Eq << apply(G, x, y)

    t = Eq[0].lhs.indices[0] - 1
    x_quote = Eq[0].lhs.base
    Eq.x_quote_definition = Equality.by_definition_of(x_quote)

    z = x_quote.definition.args[1].function.arg.base
    s = z.definition.function.function.function.arg.args[1].base

    Eq << Equality.by_definition_of(s)
    Eq.z_definition = Equality.by_definition_of(z)

    Eq << Eq[-1].subs(t, t + 1) - Eq[-1]

    Eq << Eq[-1].this.rhs.simplifier() + s[t]

    Eq << Eq.z_definition.subs(t, t + 1)
    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << Eq[-1].this.rhs.function.simplifier()

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

    Eq << Eq[-1].this.rhs.args[1].args[1].arg.simplifier()

    Eq << Eq[1].this.lhs.args[1].as_Add()

    Eq << Eq[-1].exp().reversed

    Eq << Eq.z_definition.subs(t, n - 1).summation()

    Eq << Eq[-1].this.rhs.as_Sum()

    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote.subs(t, n - 1))


# reference: Neural Architectures for Named Entity Recognition.pdf
if __name__ == '__main__':
    prove(__file__)
