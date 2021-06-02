from util import *
import axiom



@apply
def apply(given, var=None):
    lhs, rhs = given.of(Unequal)
    if var is None:
        var = given.generate_var(**lhs.type.dict)
    return Equal(KroneckerDelta(lhs, var) * KroneckerDelta(rhs, var), 0)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True)
    x = Symbol.x(integer=True, given=True)
    y = Symbol.y(integer=True, given=True)
    Eq << apply(Unequal(x, y), k)
    Eq << ~Eq[-1]

    Eq << Eq[-1].this.function.apply(algebra.is_nonzero.imply.et)

    Eq << algebra.any_et.imply.any.limits_delete.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
