from axiom.utility import plausible
from sympy.core.relational import Equal, Unequal
from sympy import Symbol

from sympy.core.numbers import oo
from sympy.logic.boolalg import Or
from sympy.concrete.expr_with_limits import ForAll, LAMBDA
import axiom
from sympy.functions.special.tensor_functions import KroneckerDelta
from sympy.matrices.expressions.matexpr import Identity
from axiom import algebre
from sympy.concrete.products import Product
from sympy.functions.elementary.piecewise import Piecewise


@plausible
def apply(*given):
    is_nonzero, forall_is_nonzero = given
    f0 = axiom.is_nonzero(is_nonzero)
    fn1, limits = axiom.forall_is_nonzero(forall_is_nonzero)
    n, fn = axiom.limits_is_nonzero(limits)    
    assert fn._subs(n, n + 1) == fn1

    assert fn._subs(n, 0) == f0
    assert n.is_nonnegative
    return Unequal(fn, 0, given=given)


from axiom.utility import check


@check
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Symbol.f(integer=True, shape=(oo,))
    Eq << apply(Unequal(f[0], 0), ForAll[n:Unequal(f[n], 0)](Unequal(f[n + 1], 0)))
    
    D = Symbol.D(definition=LAMBDA[n](KroneckerDelta(f[n], 0)))
    
    Eq.D0_is_zero = Equal(D[0], 0, plausible=True)
    
    Eq << Eq.D0_is_zero.this.lhs.definition.reversed
    
    Eq.is_multiplication_zero = Equal(D[n + 1] * (D[n] - 1), 0, plausible=True)

    Eq << algebre.is_zero.imply.ou.apply(Eq.is_multiplication_zero, simplify=False)    
    
    Eq << Eq[-1].this.args[0].lhs.definition
    
    Eq << Eq[-1].this.args[0].lhs.definition
    
    Eq << Eq[-1].this.args[0].reversed
    
    Eq << Eq[1].astype(Or)
    
    i = Symbol.i(integer=True)
    j = Symbol.j(integer=True)    
    m = Symbol.m(integer=True, positive=True)
    E = Symbol.E(definition=Identity(m) + LAMBDA[j:m, i:m](KroneckerDelta(i + 1, j) * -D[j]))
    Eq << E.this.definition
    
    Eq << (D[:m] @ E).this.expand()

    Eq << Eq[-1].this.rhs.function.function.args[1].definition
    
    Eq << Eq[-1].this.rhs.function.function.expand()
    
    Eq << Eq[-1].this.rhs().function.simplify()
    
    Eq << Eq[-1].subs(Eq.D0_is_zero)

    Eq << Eq.is_multiplication_zero.this.lhs.expand()
    
    Eq << Eq[-1].subs(n, i - 1)
    
    Eq << Eq[-3].subs(Eq[-1])

    k = Symbol.k(integer=True)    
    E_quote = Symbol("E'", definition=LAMBDA[j:m, i:m](Piecewise((Product[k:i + 1:j](D[k]), j >= i), (0, True))))
    
    Eq << Eq[-1] @ E_quote
    
    Eq << (E @ E_quote).this.expand()
    
    Eq << Eq[-1].this.rhs.function.function.args[0].definition
    
    Eq << Eq[-1].this.rhs().function.simplify()
    
    Eq << Eq[-1].this.rhs.function.function.args[0].definition
    
    Eq << Eq[-1].this.rhs.function.function.expand()
    
    Eq << (-Eq[-1].rhs.function.args[0].args[0].expr).this.astype(Product)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[-1].this.rhs.function.astype(Piecewise)

        
if __name__ == '__main__':
    prove(__file__)
