from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from sympy.utility import plausible, Sum
from sympy.core.symbol import Symbol, generate_free_symbol
from sympy.core.function import Difference, Function
from axiom.discrete.combinatorics.binomial import Pascal


def apply(fx, x, n):
    k = generate_free_symbol(fx.free_symbols | x.free_symbols | n.free_symbols, integer=True)
    return Equality(Difference(fx, x, n),
                    Sum[k:0:n]((-1) ** (n - k) * binomial(n, k) * fx.subs(x, x + k)),
                    plausible=plausible())


from sympy.utility import check


@check
def prove(Eq):
    f = Function('f')
    x = Symbol('x')
    fx = f(x)
    n = Symbol('n', integer=True, nonnegative=True)
    Eq << apply(fx, x, n)

    Eq << Eq[-1].subs(n, 0).doit()
    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-1].this.lhs.bisect(back=1)

    Eq << Eq[-1].this.lhs.expr.doit()

    Eq << Eq[-1].this.lhs.as_Add()

    Eq << Eq[0].subs(x, x + 1) - Eq[0]

    Eq << Eq[-1].subs(Eq[-2])

    k = Eq[0].rhs.limits[0][0]
    Eq << Pascal.apply(n + 1, k)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].expand()

    Eq << Eq[-1].this.lhs.args[0].args[1].simplifier()

    Eq << Eq[-1].this.rhs.args[1].args[1].simplifier()
    
    Eq << Eq[-1].this.lhs.args[1].limits_subs(k, k + 1)
    
    Eq << Eq[-1].this.rhs.simplifier()
    
    Eq << Eq[-1].this.lhs.expand()


if __name__ == '__main__':
    prove(__file__)

