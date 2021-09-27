from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Range)
    return LessEqual(a, b)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Range(a, b), a.emptySet))

    Eq << sets.range_is_nonempty.imply.lt.apply(Eq[0])
    Eq << algebra.lt.imply.le.relax.apply(Eq[-1])



if __name__ == '__main__':
    run()