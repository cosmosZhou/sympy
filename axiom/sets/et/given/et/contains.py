from util import *
import axiom



# i ∈ [d + j; n) & j ∈ [a; -d + n)
@apply
def apply(given):
    equal, contains = given.of(And)

    a, A = contains.of(Contains)
    _A, union_B_aset = equal.of(Equal)

    if A != _A:
        _A, union_B_aset = union_B_aset, _A

    B, aset = union_B_aset.of(Union)
    if aset != a.set:
        B, aset = aset, B

    return Equal(A // aset, B // aset) & Contains(a, A)


@prove
def prove(Eq):
    from axiom import sets, algebra
    a = Symbol.a(integer=True)
    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Contains(a, A) & Equal(B | a.set, A))

    Eq << Eq[1].apply(sets.contains.eq.imply.eq)

    Eq << Eq[-1].reversed

    Eq << algebra.et.imply.conds.apply(Eq[1])

    Eq << algebra.et.given.conds.apply(Eq[0])




if __name__ == '__main__':
    run()

