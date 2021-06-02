from util import *




@apply
def apply(*given):
    all_A, all_B = given
    assert all_A.is_ForAll and all_B.is_ForAll
    assert len(all_A.limits) == len(all_B.limits) == 1
    x, A = all_A.limits[0]
    _x, B = all_B.limits[0]
    assert x == _x

    assert all_A.function.is_Contains
    _x, _B = all_A.function.args

    assert x == _x and B == _B
    assert all_B.function.is_Contains
    _x, _A = all_B.function.args
    assert x == _x and A == _A

    return Equal(A, B)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.integer * n)
    B = Symbol.B(etype=dtype.integer * n)

    Eq << apply(ForAll[x:A](Contains(x, B)), ForAll[x:B](Contains(x, A)))

    Eq << sets.all_contains.imply.subset.apply(Eq[0])

    Eq << sets.all_contains.imply.subset.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

