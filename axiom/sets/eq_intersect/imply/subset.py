from util import *


@apply
def apply(given):
    (A, B), _A = given.of(Equal[Intersection])
    if _A != A:
        A, B = B, A
    assert _A == A

    return Subset(A, B)


@prove
def prove(Eq):
    from axiom import sets

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Equal(A & B, A))

    Eq << sets.subset.given.eq.intersect.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-11-21
