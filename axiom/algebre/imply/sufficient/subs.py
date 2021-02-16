from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre

@apply(imply=True, given=None)
def apply(given, old, new):
    assert old.is_symbol
    assert not old.is_given
    assert new in given.domain_defined(old)
    return Sufficient(given, given._subs(old, new))


@prove
def prove(Eq):
    n = Symbol.n(integer=True, nonnegative=True)    
    f = Function.f(nargs=(), shape=(), real=True)
    g = Function.g(nargs=(), shape=(), real=True)    
    t = Function.t(nargs=(), shape=(), real=True)
    x = Symbol.x(real=True)
    
    Eq << apply(Equal(f[n](x), g[n](x)), x, t(x))
    
    Eq << Eq[0].this.lhs.apply(algebre.equal.imply.equal.subs, x, t(x))


if __name__ == '__main__':
    prove(__file__)
