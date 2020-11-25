from sympy.functions.combinatorial.factorials import binomial
from sympy.core.relational import Equality
from axiom.utility import plausible
from sympy.core.function import Difference, Function
from axiom.discrete.combinatorics.binomial import Pascal
from sympy.concrete.summations import Sum
from sympy import Symbol, Slice
from sympy.core.add import Add

@plausible
def apply(fx, x, n):
    k = fx.generate_free_symbol(x.free_symbols | n.free_symbols, integer=True)
    return Equality(Difference(fx, x, n),
                    Sum[k:0:n]((-1) ** (n - k) * binomial(n, k) * fx.subs(x, x + k)))


from axiom.utility import check


@check
def prove(Eq):
    f = Function('f', real=True)
    x = Symbol.x(real=True)
    fx = f(x)
    assert fx.is_real
    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(fx, x, n)

    Eq << Eq[-1].subs(n, 0).doit()
    Eq << Eq[-1].subs(n, n + 1)

    Eq << Eq[-1].this.lhs.bisect(Slice[:1])

    Eq << Eq[-1].this.lhs.expr.doit()

    Eq << Eq[-1].this.lhs.astype(Add)

    Eq << Eq[0].subs(x, x + 1) - Eq[0]

    Eq << Eq[-1].subs(Eq[-2])

    k = Eq[0].rhs.limits[0][0]
    Eq << Pascal.apply(n + 1, k)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].expand()

    Eq << Eq[-1].this.lhs.args[0].args[1].simplify()

    Eq << Eq[-1].this.rhs.args[0].args[1].simplify()
    
    Eq << Eq[-1].this.lhs.args[1].limits_subs(k, k + 1)
    
    Eq << Eq[-1].this.rhs.simplify()
    
    Eq << Eq[-1].this.lhs.expand()


if __name__ == '__main__':
    prove(__file__)

