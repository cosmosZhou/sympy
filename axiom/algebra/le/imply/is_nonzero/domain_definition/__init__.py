from util import *


@apply
def apply(given): 
    from axiom.algebra.eq.imply.is_nonzero.domain_definition import find_denominator
    lhs, rhs = given.of(LessEqual)
    den = find_denominator(lhs)
    if den is None:
        den = find_denominator(rhs)
        
    return Unequal(den, 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a = Symbol.a(real=True)
    c = Symbol.c(real=True)
    b = Symbol.b(real=True)
    d = Symbol.d(real=True)
    Eq << apply(a / b + d <= c)

    Eq << sets.le.imply.contains.interval.apply(Eq[0])

    Eq << sets.contains.imply.any_eq.apply(Eq[-1])

    Eq << Eq[-1].this.function.apply(algebra.eq.imply.is_nonzero.domain_definition)


if __name__ == '__main__':
    run()
    
from . import st
