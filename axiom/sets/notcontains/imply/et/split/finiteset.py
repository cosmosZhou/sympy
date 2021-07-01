from util import *


@apply
def apply(given, index=-1):
    e, args = given.of(NotContains[FiniteSet])

    lhs = FiniteSet(*args[:index])
    rhs = FiniteSet(*args[index:])
    
    return NotContains(e, lhs).simplify(), NotContains(e, rhs).simplify()


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol.x(integer=True)
    a = Symbol.a(integer=True)
    b = Symbol.b(integer=True)
    Eq << apply(NotContains(x, {a, b}))

    

    Eq << sets.notcontains.imply.ne.apply(Eq[0])

    Eq << sets.notcontains.imply.ne.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()

