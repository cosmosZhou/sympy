from util import *


from axiom.algebra.eq.simplify.terms.common import simplify_common_terms


@apply(given=None)
def apply(given):
    assert given.is_Unequal
    return Equivalent(given, simplify_common_terms(given))


@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    x, y, a = Symbol(real=True, shape=(n,))


    Eq << apply(Unequal(x + a, y + a))

    Eq << Eq[-1].this.lhs - a


if __name__ == '__main__':
    run()
# created on 2020-02-03
# updated on 2020-02-03
