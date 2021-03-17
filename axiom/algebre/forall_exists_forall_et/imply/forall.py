from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebre, sets


@apply
def apply(given, index=None):
    (fn, *limits_e), *limits_f = axiom.forall_exists(given)
    et, *limits = axiom.forall_et(fn)
    
    eqs = et.args
    if index is None:
        eqs = tuple(ForAll(Exists(ForAll(eq, *limits), *limits_e), *limits_f) for eq in eqs)
        return eqs
    
    eq = eqs[index]
    
    return ForAll(Exists(ForAll(eq, *limits), *limits_e), *limits_f)


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    z = Symbol.z(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    
    f = Function.f(shape=(), real=True)
    g = Function.g(shape=(), real=True)
    
    Eq << apply(ForAll[x:0:a](Exists[y:0:b](ForAll[z:0:c]((g(x, y, z) <= 1) & (f(x, y, z) >= 1)))), index=0)
    
    Eq << Eq[0].this.function.function.apply(algebre.forall_et.imply.et, depth=0)
    
    Eq << Eq[-1].this.function.apply(algebre.exists_et.imply.et.split, depth=0)
    
    Eq << algebre.forall_et.imply.forall.apply(Eq[-1], index=0)


if __name__ == '__main__':
    prove(__file__)

