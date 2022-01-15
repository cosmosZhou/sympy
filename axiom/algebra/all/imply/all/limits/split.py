from util import *


def split(given, index=-1):
    function, (x, s) = given.of(All)

    domain, size = s.of(CartesianSpace)

    x, indices = x.of(Sliced)

    start, stop = indices
    assert size == stop - start

    if isinstance(index, slice):
        _start = index.start
        _stop = index.stop

        limits = [(x[start:_start], CartesianSpace(domain, _start - start)),
                  (x[index], CartesianSpace(domain, _stop - start))]
    else:
        if index < 0:
            index += x.shape[0]

        limits = [(x[start:index], CartesianSpace(domain, index - start)), (x[index], domain)]

        _stop = index + 1

    if _stop < stop:
        limits.append((x[_stop:stop], CartesianSpace(domain, stop - _stop)))

    return All(function, *limits)


@apply
def apply(given, index=-1):
    return split(given, index)


@prove
def prove(Eq):
    from axiom import algebra
    n = Symbol(integer=True, positive=True)
    a, b = Symbol(real=True)

    x = Symbol(real=True, shape=(oo,))
    f = Function(real=True)

    Eq << apply(All[x[:n + 1]:CartesianSpace(Interval(a, b), n + 1)](f(x[:n + 1]) > 0), index=n)

    Eq << algebra.all.imply.infer.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(algebra.all.given.et, cond={n})

    Eq << algebra.all.given.infer.apply(Eq[1])

    Eq << Eq[-1].this.lhs.args[0].simplify()


if __name__ == '__main__':
    run()

# created on 2018-12-07
