from util import *


def merge(given):
    function, *limits = given.of(All)

    limit_slice, limit_index = limits

    if not limit_slice[0].is_Slice:
        limit_index, limit_slice = limits

    x_slice, space = limit_slice
    _domain, n = space.of(CartesianSpace)

    x, slices = x_slice.of(Slice)

    if len(limit_index) == 3:
        x_index, a, b = limit_index
        integer = x_index.is_integer
        domain = (Range if integer else Interval)(a, b)
        _x, index = x_index.args
    else:
        x_index, domain = limit_index
        if x_index.is_Slice:
            domain, size = domain.of(CartesianSpace)
            assert size == x_index.shape[0]
            _x, index = x_index.args
        else:
            _x, index = x_index.of(Indexed)

    assert _domain == domain

    assert _x == x

    start, stop = slices
    if index == stop:
        stop += 1
    elif index == start - 1:
        start = index
    else:
        assert index.is_Tuple
        _start, _stop = index
        assert _stop == start
        start = _start

    return All[x[start:stop]:CartesianSpace(domain, stop - start)](function)


@apply
def apply(given):
    return merge(given)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)

    x = Symbol.x(real=True, shape=(oo,))
    f = Function.f(real=True)

    Eq << apply(All[x[:n]:CartesianSpace(Interval(a, b), n), x[n]:Interval(a, b)](f(x[:n + 1]) > 0))

    Eq << algebra.all.given.suffice.apply(Eq[1])

    Eq << Eq[-1].this.lhs.apply(algebra.all.imply.et.split, cond={n})

    Eq << algebra.all.imply.suffice.apply(Eq[0])

    Eq << Eq[-1].this.lhs.args[0].simplify()


if __name__ == '__main__':
    run()

