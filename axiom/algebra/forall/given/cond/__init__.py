from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given):
    fn, *limits = axiom.is_ForAll(given)
    return fn


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(ForAll[e:S](f(e) > 0))
    
    Eq << algebra.forall.given.ou.apply(Eq[0])
    
    Eq << algebra.ou.given.cond.apply(Eq[-1], index=1)


if __name__ == '__main__':
    prove()

from . import subs