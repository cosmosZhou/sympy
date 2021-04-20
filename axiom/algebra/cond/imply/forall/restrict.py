from sympy import *
from axiom.utility import prove, apply
import axiom
from axiom import algebra


@apply
def apply(given, *limits):
    limits = [*limits]
    for i, (x, *ab) in enumerate(limits):
        if not ab:
            if x.domain:
                limits[i] = (x, x.domain)
    return ForAll(given, *limits)


@prove
def prove(Eq):
    S = Symbol.S(etype=dtype.real)
    e = Symbol.e(real=True)
    f = Function.f(shape=(), integer=True)

    Eq << apply(f(e) > 0, (e, S))
    
    Eq << Eq[0].apply(algebra.cond.imply.et.forall, cond=Contains(e, S))
    
    Eq << algebra.et.imply.cond.apply(Eq[-1])


if __name__ == '__main__':
    prove()

