from sympy import *
from axiom.utility import prove, apply
from axiom import algebre, discrete


@apply(imply=True)
def apply(fx, x, n):
    k = fx.generate_free_symbol(x.free_symbols | n.free_symbols, integer=True)
    return Equality(Difference(fx, x, n),
                    Sum[k:0:n + 1]((-1) ** (n - k) * binomial(n, k) * fx.subs(x, x + k)))


@prove
def prove(Eq):
    f = Function('f', real=True)
    x = Symbol.x(real=True)
    fx = f(x)
    assert fx.is_real
    n = Symbol.n(integer=True, nonnegative=True)
    Eq << apply(fx, x, n)

    Eq.initial = Eq[0].subs(n, 0)
    
    Eq << Eq.initial.doit()
    
    Eq.induction = Eq[0].subs(n, n + 1)

    Eq << Eq.induction.this.lhs.bisect(Slice[:1])

    Eq << Eq[-1].this.lhs.expr.doit()

    Eq << Eq[-1].this.lhs.astype(Add)

    Eq.hypothesis = Eq[0].subs(x, x + 1)
    
    Eq << Eq.hypothesis - Eq[0]

    Eq << Eq[-1].subs(Eq[-2])

    k = Eq[0].rhs.limits[0][0]
    Eq << discrete.combinatorics.binomial.Pascal.apply(n + 1, k)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].expand()

    Eq << Eq[-1].this.lhs.args[0].args[1].simplify()

    Eq << Eq[-1].this.rhs.args[0].args[1].simplify()
    
    Eq << Eq[-1].this.lhs.args[1].limits_subs(k, k + 1)
    
    Eq << Eq[-1].this.rhs.simplify()
    
    Eq << Eq[-1].this.lhs.expand()
    
#     if Eq.induction.given is not None:
    Eq << Eq.induction.induct()
#     elif Eq.hypothesis.given is not None:
#         Eq << Eq.hypothesis.induct(reverse=True).split()[0]
#     elif Eq[0].given is not None:
#         Eq << Eq[0].induct(reverse=True).split()[0]        
        
    Eq << algebre.equal.sufficient.imply.et.induction.apply(Eq.initial, Eq[-1], n=n, x=x).split()


if __name__ == '__main__':
    prove(__file__)

