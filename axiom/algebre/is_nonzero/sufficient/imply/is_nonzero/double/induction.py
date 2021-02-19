from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre


@apply
def apply(*given, n=None, m=None):
    f0, sufficient = given
    axiom.is_nonzero(f0)
    fn, fn1 = axiom.is_Sufficient(sufficient)
    fn = fn._subs(m, m - 1)
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, 0) == f0
    assert n.domain.min() == 0
    
    return fn


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True, given=False)    
    m = Symbol.m(integer=True, nonnegative=True)
    f = Symbol.f(integer=True, shape=(oo, oo))
    Eq << apply(Unequal(f[m, 0], 0), Sufficient(Unequal(f[m + 1, n], 0), Unequal(f[m, n + 1], 0)), n=n, m=m)
    
    B = Symbol.B(definition=LAMBDA[n, m](KroneckerDelta(f[m, n], 0)))
    
    Eq << B[m, 0].this.definition
    
    Eq << algebre.unequal.imply.is_zero.kronecker_delta.single.apply(Eq[0], simplify=False)
    
    Eq.initial_B = Eq[-1] + Eq[-2]
    
    Eq.or_statement = Or(Equal(B[m, n + 1], 0), Equal(B[m + 1, n], 1), plausible=True)
    
    Eq << Eq.or_statement.this.args[1].lhs.definition
    
    Eq << Eq[-1].this.args[0].lhs.definition
    
    Eq << Eq[-1].this.args[0].reversed
    
    Eq << Eq[1].astype(Or)
    
    Eq.is_multiplication_zero = algebre.ou.imply.is_zero.apply(Eq.or_statement)

    D = Symbol.D(definition=LAMBDA[n, m](Piecewise((B[m - n, n], m >= n), (0, True))))
    
    Eq << D[m, 0].this.definition

    Eq.initial_D = Eq[-1] + Eq.initial_B
    
    Eq.hypothesis = Equal(D[m, n], 0, plausible=True)
    
    Eq.induction = Equal(D[m, n + 1], 0, plausible=True)
    
    Eq.equality = Equal((D[m, n] - 1) * D[m, n + 1], 0, plausible=True)
    
    Eq << Eq.equality.this.lhs.args[1].args[1].definition
    
    Eq << Eq[-1].this.lhs.args[1].astype(Piecewise)
    
    Eq << Eq[-1].this.lhs.args[0].definition
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << Eq.is_multiplication_zero.subs(m, m - 1 - n)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq.equality.subs(Eq.hypothesis).reversed
    
    Eq << Eq.induction.induct()

    Eq << algebre.is_zero.sufficient.imply.is_zero.induction.apply(Eq.initial_D, Eq[-1], n=n)
    
    Eq << Eq.hypothesis.this.lhs.definition
    
    Eq << Eq[-1].subs(m, m + n)
    
    Eq << Eq[-1].this.lhs.definition

    
if __name__ == '__main__':
    prove(__file__)
