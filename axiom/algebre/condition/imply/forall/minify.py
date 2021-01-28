
from axiom.utility import prove, apply
from sympy.core.symbol import dtype

from sympy import Symbol, ForAll, Contains
from sympy.core.function import Function
from sympy.core.containers import Tuple
import axiom


@apply(imply=True)
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
    f = Function.f(nargs=(), shape=(), integer=True)

    Eq << apply(f(e) > 0, (e, S))
    
    Eq << Eq[0].bisect(Contains(e, S))
    
    Eq << Eq[-1].split()


if __name__ == '__main__':
    prove(__file__)

