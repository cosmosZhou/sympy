from util import *




@apply
def apply(all_A, all_B):
    (_x, _B), (x, A) = all_A.of(All[Contains])    
    (___x, _A), (__x, B) = all_B.of(All[Contains])
    assert x == _x == __x == ___x
    assert B == _B
    assert A == _A

    return Equal(A, B)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(complex=True, shape=(n,))
    A = Symbol.A(etype=dtype.integer * n)
    B = Symbol.B(etype=dtype.integer * n)

    Eq << apply(All[x:A](Contains(x, B)), All[x:B](Contains(x, A)))

    Eq << sets.all_contains.imply.subset.apply(Eq[0])

    Eq << sets.all_contains.imply.subset.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

