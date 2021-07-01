from util import *



# given: A in B
# => A | B = B
@apply
def apply(contains, forall):
    function, *limits = forall.of(All)
    b, A = contains.of(Contains)

    index = -1
    for i, (x, *domain) in enumerate(limits):
        if len(domain) == 1:
            if domain[0] == A:
                index = i
                break

    assert index >= 0

    function = function._subs(x, b) if x != b else function
    limits = [*forall.limits]
    del limits[index]
    if limits:
        return All(function, *limits)

    return function


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(complex=True, positive=True)
    A = Symbol.A(etype=dtype.complex * n)
    a = Symbol.a(complex=True, shape=(n,))
    b = Symbol.b(complex=True, shape=(n,))

    f = Function.f(complex=True, shape=())

    assert f.is_complex
    assert f.shape == ()

    Eq << apply(Contains(b, A), All[a:A](Equal(f(a), 1)))

    Eq << algebra.all.imply.ou.subs.apply(Eq[1], a, b)

    Eq <<= Eq[-1] & Eq[0]

    Eq << algebra.et.imply.et.apply(Eq[-1])


if __name__ == '__main__':
    run()

