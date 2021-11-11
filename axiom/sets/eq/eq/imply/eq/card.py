from util import *



@apply
def apply(equality_A, equality_B):
    assert equality_A.is_Equal and equality_B.is_Equal
    image_B, A = equality_A.args
    image_A, B = equality_B.args

    gb, b, _B = image_B.image_set()
    fb, a, _A = image_A.image_set()

    assert A == _A and B == _B

    return Equal(Card(A), Card(B))




@prove
def prove(Eq):
    from axiom import sets
    n, m = Symbol(integer=True, positive=True)
    A = Symbol(etype=dtype.integer * n)
    a = Symbol(integer=True, shape=(n,))

    B = Symbol(etype=dtype.integer * m)
    b = Symbol(integer=True, shape=(m,))

    f = Function(integer=True, shape=(m,))
    g = Function(integer=True, shape=(n,))

    Eq << apply(Equal(Cup[a:A](f(a).set), B), Equal(Cup[b:B](g(b).set), A))

    Eq << sets.imply.le.cup.apply(*Eq[0].lhs.args)

    Eq << Eq[-1].subs(Eq[0])

    Eq << sets.imply.le.cup.apply(*Eq[1].lhs.args)

    Eq << Eq[-1].subs(Eq[1])

    Eq <<= Eq[-3] & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2020-07-31
# updated on 2020-07-31
