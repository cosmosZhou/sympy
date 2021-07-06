from util import *

# given: |A| >= 1
# A != {}


@apply
def apply(given):
    assert isinstance(given, GreaterEqual)
    S_abs, positive = given.args
    assert S_abs.is_Abs and positive.is_extended_positive
    S = S_abs.arg

    x = S.element_symbol()

    return Unequal(S, S.etype.emptySet)


@prove
def prove(Eq):
    from axiom import sets, algebra
    S = Symbol.S(etype=dtype.integer, given=True)

    Eq << apply(abs(S) >= 1)

    Eq << algebra.ge.imply.gt.relax.apply(Eq[0], 0)

    Eq << sets.is_positive.imply.is_nonemptyset.apply(Eq[-1])


if __name__ == '__main__':
    run()

