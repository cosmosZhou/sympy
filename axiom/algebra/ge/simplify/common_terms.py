from util import *


from axiom.algebra.eq.simplify.terms.common import simplify_common_terms


@apply(given=None)
def apply(given):
    assert given.is_GreaterEqual
    return Equivalent(given, simplify_common_terms(given))


@prove
def prove(Eq):
    x, y, a = Symbol(real=True)


    Eq << apply(GreaterEqual(x + a, y + a))

    Eq << Eq[-1].this.lhs - a


if __name__ == '__main__':
    run()
