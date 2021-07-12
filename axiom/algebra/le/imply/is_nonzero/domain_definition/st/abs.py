from util import *


@apply
def apply(given): 
    from axiom.algebra.eq.imply.is_nonzero.domain_definition import find_denominator
    num, rhs = given.of(LessEqual[Abs, Expr])
    den = find_denominator(num)
        
    return Unequal(den, 0)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(real=True)
    c = Symbol.c(real=True)
    b = Symbol.b(real=True)
    d = Symbol.d(real=True)
    Eq << apply(abs(a / b + d) <= c)

    Eq << algebra.le.imply.et.split.abs.apply(Eq[0])

    Eq << algebra.le.imply.is_nonzero.domain_definition.apply(Eq[-2])


if __name__ == '__main__':
    run()