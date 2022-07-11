from util import *


def limits_union(limits, _limits, function=None):
    new_limits = []
    assert len(limits) == len(_limits)

    for limit, _limit in zip(limits, _limits):
        x, domain = limit.coerce_setlimit(function=function)
        _x, _domain = _limit.coerce_setlimit(function=function)

        assert x == _x
        assert not _domain & domain
        new_limits.append((x, domain | _domain))

    return new_limits


@apply
def apply(self):
    A, B = self.of(Add)
    function, *limits_a = A.of(Sum)
    _function, *limits_b = B.of(Sum)
    assert function == _function

    limits = limits_union(limits_a, limits_b, function=function)
    return Equal(self, Sum(function, *limits), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    f = Function(integer=True)
    Eq << apply(Add(Sum[k:A - B](f(k)), Sum[k:A & B](f(k))))

    Eq << Eq[0].this.find(Sum).apply(algebra.sum.bool)

    Eq << Eq[-1].this.lhs.find(Sum).apply(algebra.sum.bool)

    Eq << Eq[-1].this.find(Sum + ~Sum).apply(algebra.sum.bool)

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.sum)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Add).apply(algebra.add.principle.inclusive_exclusive)


if __name__ == '__main__':
    run()
# created on 2018-08-09
