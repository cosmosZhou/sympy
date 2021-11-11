from util import *


@apply
def apply(eq_sum, eq_union, x=None):
    w_sum, M = eq_sum.of(Equal)
    w_union, M_interval = eq_union.of(Equal)

    zero, _M = M_interval.of(Range)
    assert _M == M
    assert zero == 0

    wi_abs, limit = w_sum.of(Sum)
    wi, _limit = w_union.of(Cup)

    assert limit == _limit

    _wi = wi_abs.of(Card)
    assert _wi == wi

    (i,) = limit
    w, _i = wi.of(Indexed)
    assert _i == i

    _M = x.shape[0]
    assert _M == M

    j = Symbol(integer=True)

    k = w.shape[0]

    return Equivalent(Element(j, w[i]) & Element(i, Range(k)),
                      Equal(i, Sum[i](i * Bool(Element(j, w[i])))) & Element(j, Range(M)))


@prove(proved=False)
def prove(Eq):
    M, n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    k = Symbol(domain=Range(M))
    x = Symbol(real=True, shape=(M, n))
    omega = Symbol(shape=(k,), etype=dtype.integer, empty=False)
    Eq << apply(Equal(Sum[i](Card(omega[i])), M), Equal(Cup[i](omega[i]), k.domain), x=x)


if __name__ == '__main__':
    run()

from . import w_quote
# created on 2020-12-24
# updated on 2020-12-24
