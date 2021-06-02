from util import *


@apply
def apply(given):
    assert given.is_Contains
    e, domain = given.args
    A, B = domain.of(Complement)

    return And(Contains(e, A), NotContains(e, B))


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol.e(integer=True, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)
    B = Symbol.B(etype=dtype.integer, given=True)
    Eq << apply(Contains(e, A // B))

    Eq << algebra.et.imply.conds.apply(Eq[-1])

    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    run()

