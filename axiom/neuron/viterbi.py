
from sympy.core.symbol import Symbol

from sympy.utility import plausible
from sympy.core.relational import Equality

from sympy.core.numbers import oo
from sympy.concrete.expr_with_limits import Ref, MIN
from sympy.concrete.summations import Sum


@plausible
def apply(G, x, y):
    _, d = x.shape
    i = Symbol('i', integer=True)
    t = Symbol('t', integer=True, nonnegative=True)

    s = Symbol('s', shape=(oo,),
                    definition=Ref[t](Sum[i:1:t](G[y[i], y[i - 1]]) + Sum[i:0:t](x[i, y[i]])))

    x_quote = Symbol("x'", shape=(oo, d), definition=Ref[y[t], t](MIN[y[0:t]](s[t])))

    return Equality(x_quote[t + 1], x[t + 1] + MIN(x_quote[t] + G)), \
        Equality(MIN[y[:t + 1]](s[t]), MIN(x_quote[t]))


from sympy.utility import check


@check
def prove(Eq):
    d = Symbol('d', integer=True)

    # oo is the length of the sequence
    # d is the number of output labels
    G = Symbol('G', shape=(d, d), real=True)
    x = Symbol('x', shape=(oo, d), real=True)
    y = Symbol('y', shape=(oo,), real=True)

    Eq.s_definition, Eq.x_quote_definition, Eq.recursion, Eq.aggregate = apply(G, x, y)
    
    Eq.x_quote_definition = Eq.x_quote_definition.reference((Eq.x_quote_definition.lhs.indices[-1],))
    
    s = Eq.x_quote_definition.rhs.function.function.base

    t = Eq.recursion.lhs.indices[0] - 1
    Eq << Eq.s_definition.subs(t, t + 1)

    Eq << Eq[-1] - Eq.s_definition

    Eq << Eq[-1].this.rhs.simplify() + s[t]

    Eq << Eq.x_quote_definition.subs(t, t + 1)

    Eq << Eq[-1].this.rhs.subs(Eq[-2])

    Eq << Eq[-1].this.rhs.function.simplify()

    Eq << Eq[-1].this.rhs.args[1].function.bisect(back=1)

    Eq << Eq[-1].this.rhs.args[1].function.as_Ref()

    Eq << Eq[-1].this.rhs.args[1].as_Min()

    Eq << Eq[-1].this.rhs.subs(Eq.x_quote_definition.reversed)

    Eq << Eq.aggregate.this.lhs.bisect(back=1)

    Eq << Eq[-1].this.lhs.as_Ref()

    Eq << Eq[-1].subs(Eq.x_quote_definition.reversed)


if __name__ == '__main__':
    prove(__file__)
