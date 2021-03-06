from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply(imply=True)
def apply(*given, n=None):
    f0, sufficient = given
    axiom.is_nonzero(f0)
    fn, fn1 = axiom.is_Sufficient(sufficient)    
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, 0) == f0
    assert n.domain.min() == 0
    
    return fn


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    Eq << apply(Unequal(f[0], 0), Sufficient(Unequal(f[n], 0), Unequal(f[n + 1], 0)), n=n)
    
    D = Symbol.D(definition=LAMBDA[n](KroneckerDelta(f[n], 0)))

    Eq.D0_is_zero = Equal(D[0], 0, plausible=True)
    
    Eq << Eq.D0_is_zero.this.lhs.definition
    
    Eq.or_statement = Or(Equal(D[n + 1], 0), Equal(D[n], 1), plausible=True)
    
    Eq << Eq.or_statement.this.args[0].lhs.definition
    
    Eq << Eq[-1].this.args[0].lhs.definition
    
    Eq << Eq[-1].this.args[0].reversed

    Eq << Eq[1].astype(Or)
    
    Eq.is_multiplication_zero = algebre.ou.imply.is_zero.apply(Eq.or_statement)
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    m = Symbol.m(integer=True, positive=True)
    E = Symbol.E(definition=Identity(m) + LAMBDA[j:m, i:m](KroneckerDelta(i + 1, j) * -D[j]))
    Eq << E.this.definition
    
    Eq << (D[:m] @ E).this.expand()

    Eq << Eq[-1].this.rhs.function.function.args[1].definition
    
    Eq << Eq[-1].this.rhs.function.function.expand()
    
    Eq << Eq[-1].this.rhs().function.simplify()
    
    Eq << Eq[-1].this.rhs.astype(LAMBDA)
    
    Eq << Eq[-1].this.rhs.function.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs.function.apply(algebre.imply.equal.piecewise.swap.front)    
    
    Eq << Eq[-1].this.rhs().function.args[0].cond.simplify()
    
    Eq << Eq[-1].this.rhs.function.apply(algebre.imply.equal.piecewise.subs)    
    
    Eq << Eq[-1].subs(Eq.D0_is_zero)

    Eq << Eq.is_multiplication_zero.this.lhs.expand()
    
    Eq << Eq[-1].subs(n, i - 1)
    
    Eq << Eq[-3].subs(Eq[-1].reversed)

    k = Symbol.k(integer=True)    
    E_quote = Symbol("E'", definition=LAMBDA[j:m, i:m](Piecewise((Product[k:i + 1:j + 1](D[k]), j >= i), (0, True))))
    
    Eq.D_is_zero = Eq[-1] @ E_quote
    
    Eq << (E @ E_quote).this.expand()
    
    Eq << Eq[-1].this.rhs.function.function.args[0].definition
    
    Eq << Eq[-1].this.rhs().function.simplify()
    
    Eq << Eq[-1].this.rhs.function.function.args[0].definition
    
    Eq << Eq[-1].this.rhs.function.function.expand()
    
    Eq << (-Eq[-1].rhs.function.args[0].args[0].expr).this.astype(Product)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs().function.astype(Piecewise)
    
    Eq << Eq[-1].this.rhs().function.simplify(wrt=True)
    
    Eq << algebre.imply.equal.piecewise.swap.front.apply(Eq[-1].rhs.function)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs().function.simplify()
    
    Eq << Eq[-1].this.rhs.apply(algebre.imply.equal.lamda.astype.identity)

    Eq << Eq.D_is_zero.subs(Eq[-1])
    
    Eq << Eq[-1][m - 1]
    
    Eq << Eq[-1].subs(m, n + 1)
    
    Eq << Eq[-1].this.lhs.definition

        
if __name__ == '__main__':
    prove(__file__)
