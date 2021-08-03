from util import *


@apply
def apply(is_nonzero):
    ceiling = is_nonzero.of(Unequal[0])
    ((A, B), pi2), half = ceiling.of(Ceiling[(Arg + Arg) * Expr - Expr])
    assert half * 2 == 1
    assert 1 / pi2 == S.Pi * 2
    
    return Equal(ceiling, 1) | Equal(ceiling, -1)


@prove
def prove(Eq):
    from axiom import sets, algebra

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Unequal(Ceiling((Arg(A) + Arg(B)) / (S.Pi * 2) - S.One / 2), 0))

    Eq <<= sets.imply.contains.arg.apply(A), sets.imply.contains.arg.apply(B)

    Eq << sets.contains.contains.imply.contains.add.interval.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << sets.contains.imply.contains.div.interval.apply(Eq[-1], S.Pi * 2)

    Eq << sets.contains.imply.contains.sub.apply(Eq[-1], S.One / 2)

    Eq << sets.contains.imply.contains.ceiling.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(sets.range.to.finiteset)

    Eq << sets.contains.imply.ou.split.finiteset.apply(Eq[-1])

    Eq << algebra.cond.ou.imply.cond.apply(Eq[0], Eq[-1])

    


if __name__ == '__main__':
    run()