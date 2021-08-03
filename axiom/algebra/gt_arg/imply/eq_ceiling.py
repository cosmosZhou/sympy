from util import *


@apply
def apply(gt):
    A, B = gt.of(Arg + Arg > Pi)
    return Equal(Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 1)


@prove
def prove(Eq):
    from axiom import sets

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Arg(A) + Arg(B) > S.Pi)

    Eq <<= sets.imply.contains.arg.apply(A), sets.imply.contains.arg.apply(B)

    Eq << sets.contains.contains.imply.contains.add.interval.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << sets.contains.imply.contains.div.interval.apply(Eq[-1], S.Pi * 2)

    Eq << Eq[0] / (S.Pi * 2)

    Eq << sets.gt.contains.imply.contains.intersect.apply(Eq[-1], Eq[-2])
    Eq << sets.contains.imply.contains.ceiling.apply(Eq[-1])


if __name__ == '__main__':
    run()