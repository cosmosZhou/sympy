from util import *




@apply
def apply(all_A, all_B):
    (_x, _B), (x, A) = all_A.of(All[Element])
    (___x, _A), (__x, B) = all_B.of(All[Element])
    assert x == _x == __x == ___x
    assert B == _B
    assert A == _A

    return Equal(A, B)


@prove
def prove(Eq):
    from axiom import sets
    n = Symbol(integer=True, positive=True)
    x = Symbol(complex=True, shape=(n,))
    A, B = Symbol(etype=dtype.integer * n)

    Eq << apply(All[x:A](Element(x, B)), All[x:B](Element(x, A)))

    Eq << sets.all_el.imply.subset.apply(Eq[0])

    Eq << sets.all_el.imply.subset.apply(Eq[1])

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2018-04-27
# updated on 2018-04-27
