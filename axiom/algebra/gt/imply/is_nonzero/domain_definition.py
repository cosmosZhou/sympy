from util import *


@apply
def apply(given): 
    (num, den), rhs = given.of(Greater[Expr / Expr, Expr])
        
    return Unequal(den, 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a = Symbol.a(real=True)
    c = Symbol.c(real=True)
    b = Symbol.b(real=True)
    Eq << apply(a / b > c)

    Eq << sets.gt.imply.contains.interval.apply(Eq[0])

    Eq << sets.contains.imply.any_eq.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(algebra.eq.imply.is_nonzero.domain_definition)


if __name__ == '__main__':
    run()