from util import *



@apply
def apply(imply, i=None):
    x, y = imply.of(Equal)
    assert x.shape == y.shape

    if isinstance(i, (tuple, Tuple)):
        shape = x.shape
        for i_, n in zip(i, shape):
            assert i_.domain == Range(0, n)
    else:
        n = x.shape[0]
        assert i.domain == Range(0, n)

    return Equal(x[i], y[i])


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True, given=True)
    a = Symbol.a(shape=(n,), etype=dtype.integer)
    b = Symbol.b(shape=(n,), etype=dtype.integer)
    i = Symbol.i(domain=Range(0, n))

    Eq << apply(Equal(a, b), i=i)

    Eq << algebra.eq.imply.eq.lamda.apply(Eq[1], (i,))


if __name__ == '__main__':
    run()

