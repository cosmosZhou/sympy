from util import *


@apply
def apply(complement):
    U, C = complement.of(Complement)
    n = C.variable
    cond = C.condition
#     eq__0mod_x2
    assert cond.of(Equal[Basic % 2, 0]) == n
    base_set = C.base_set
    assert base_set.is_UniversalSet

    return Equal(complement, conditionset(n, Equal(n % 2, 1), U))


@prove
def prove(Eq):
    from axiom import sets, algebra
    U = Symbol.U(etype=dtype.integer, given=True)
    n = Symbol.n(integer=True, given=True)

    Eq << apply(Complement(U, conditionset(n, Equal(n % 2, 0))))

    A = Symbol.A(Eq[0].lhs)
    B = Symbol.B(Eq[0].rhs)

    Eq.all_contains_in_B = ForAll[n:A](Contains(n, B), plausible=True)

    Eq << Eq.all_contains_in_B.this.limits[0][1].definition

    Eq << Eq[-1].this.function.rhs.definition

    Eq << algebra.all.given.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[1].apply(sets.notcontains.given.ou.split.complement)

    Eq << ~Eq[-1]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(algebra.is_nonzero.imply.is_odd)

    Eq.all_contains_in_A = ForAll[n:B](Contains(n, A), plausible=True)

    Eq << Eq.all_contains_in_A.this.limits[0][1].definition

    Eq << Eq[-1].this.function.rhs.definition

    Eq << algebra.all.given.ou.apply(Eq[-1])

    Eq << sets.all_contains.all_contains.imply.eq.apply(Eq.all_contains_in_A, Eq.all_contains_in_B)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

