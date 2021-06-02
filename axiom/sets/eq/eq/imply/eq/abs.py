from util import *



@apply
def apply(*given):
    equality_A, equality_B = given
    assert equality_A.is_Equal and equality_B.is_Equal
    image_B, A = equality_A.args
    image_A, B = equality_B.args

    gb, b, _B = image_B.image_set()
    fb, a, _A = image_A.image_set()

    assert A == _A and B == _B

    return Equal(Abs(A), Abs(B))




@prove
def prove(Eq):
    from axiom import sets
    n = Symbol.n(integer=True, positive=True)
    m = Symbol.m(integer=True, positive=True)
    A = Symbol.A(etype=dtype.integer * n)
    a = Symbol.a(integer=True, shape=(n,))
    B = Symbol.B(etype=dtype.integer * m)
    b = Symbol.b(integer=True, shape=(m,))

    f = Function.f(nargs=(n,), integer=True, shape=(m,))
    g = Function.g(nargs=(m,), integer=True, shape=(n,))

    assert f.is_integer
    assert g.is_integer
    assert f.shape == (m,)
    assert g.shape == (n,)

    Eq << apply(Equal(Cup[a:A](f(a).set), B), Equal(Cup[b:B](g(b).set), A))

    Eq << sets.imply.le.cup.apply(*Eq[0].lhs.args)

    Eq << Eq[-1].subs(Eq[0])

    Eq << sets.imply.le.cup.apply(*Eq[1].lhs.args)

    Eq << Eq[-1].subs(Eq[1])

    Eq <<= Eq[-3] & Eq[-1]


if __name__ == '__main__':
    run()

