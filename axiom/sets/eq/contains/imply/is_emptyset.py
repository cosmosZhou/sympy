from util import *


@apply
def apply(equal, contains):
    if contains.is_Equal:
        contains, equal = equal, contains

    a, A = contains.of(Contains)

    _A = equal.of(Equal[Abs, 1])
    assert _A == A
    return Equal(A - a.set, a.emptySet)


@prove
def prove(Eq):
    from axiom import sets

    A = Symbol.A(etype=dtype.integer, given=True)
    a = Symbol.a(integer=True, given=True)
    Eq << apply(Equal(abs(A), 1), Contains(a, A))

    Eq << sets.eq.contains.imply.eq.finiteset.apply(Eq[0], Eq[1])

    Eq << sets.eq.imply.eq.complement.apply(Eq[-1], a.set)

    

    

    


if __name__ == '__main__':
    run()