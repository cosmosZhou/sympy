from util import *


@apply(simplify=False)
def apply(given, var=None):
    lhs, rhs = given.of(Unequal)
    if var is None:
        var = given.generate_var(**lhs.type.dict)
    return Equal(KroneckerDelta(lhs, var) * KroneckerDelta(rhs, var), 0)


@prove
def prove(Eq):
    from axiom import algebra

    k = Symbol(integer=True)
    x, y = Symbol(integer=True, given=True)
    Eq << apply(Unequal(x, y), k)

    Eq << ~Eq[-1]

    Eq << Eq[-1].this.expr.apply(algebra.ne_zero.imply.et)

    Eq << algebra.any_et.imply.any.limits_delete.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2020-02-06
