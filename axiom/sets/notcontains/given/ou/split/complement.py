from util import *



# given e not in S
@apply
def apply(imply):
    e, S = imply.of(NotContains)
    U, A = S.of(Complement)
    return Or(NotContains(e, U), Contains(e, A).simplify())


@prove
def prove(Eq):
    from axiom import algebra
    e = Symbol.e(integer=True, given=True)
    U = Symbol.U(etype=dtype.integer, given=True)
    A = Symbol.A(etype=dtype.integer, given=True)

    Eq << apply(NotContains(e, Complement(U, A)))

    Eq << ~Eq[0]

    Eq <<= Eq[-1] & Eq[1]

    Eq << algebra.et.imply.ou.apply(Eq[-1])


if __name__ == '__main__':
    run()

