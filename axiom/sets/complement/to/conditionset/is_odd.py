from util import *


@apply
def apply(complement):
    U, C = complement.of(Complement)
    n = C.variable
    cond = C.condition
#     eq__0mod_x2
    assert cond.of(Equal[Expr % 2, 0]) == n
    base_set = C.base_set
    assert base_set.is_UniversalSet

    return Equal(complement, conditionset(n, Equal(n % 2, 1), U))


@prove
def prove(Eq):
    from axiom import sets, algebra
    U = Symbol(etype=dtype.integer, given=True)
    n = Symbol(integer=True, given=True)

    Eq << apply(Complement(U, conditionset(n, Equal(n % 2, 0))))

    A = Symbol(Eq[0].lhs)
    B = Symbol(Eq[0].rhs)

    Eq.all_contains_in_B = All[n:A](Element(n, B), plausible=True)

    Eq << Eq.all_contains_in_B.this.limits[0][1].definition

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << algebra.all.given.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[1].apply(sets.notin.given.ou.split.complement)

    Eq << ~Eq[-1]

    Eq << algebra.et.imply.ou.apply(Eq[-1])

    Eq << Eq[-1].this.args[0].apply(algebra.mod_is_nonzero.imply.is_odd)

    Eq.all_contains_in_A = All[n:B](Element(n, A), plausible=True)

    Eq << Eq.all_contains_in_A.this.limits[0][1].definition

    Eq << Eq[-1].this.expr.rhs.definition

    Eq << algebra.all.given.ou.apply(Eq[-1])

    Eq << sets.all_el.all_el.imply.eq.apply(Eq.all_contains_in_A, Eq.all_contains_in_B)

    Eq << Eq[-1].this.lhs.definition

    Eq << Eq[-1].this.rhs.definition

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

