from util import *
import axiom


def absorb(Sum, self):
    assert isinstance(self, Sum.operator)

    sum_fx, fi = self.args
    if not isinstance(sum_fx, Sum):
        sum_fx, fi = fi, sum_fx
        assert isinstance(sum_fx, Sum)
        assert not isinstance(fi, Sum)

    fx, *limits = sum_fx.args
    k, a, b = axiom.limit_is_Interval(limits)
    assert fx._subs(k, a - 1) == fi
    return Sum[k:a - 1:b](fx)

@apply
def apply(self):
    return Equal(self, absorb(Sum, self), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra
    k = Symbol.k(integer=True)
    n = Symbol.n(integer=True)
    i = Symbol.i(domain=Range(0, n))
    f = Function.f(integer=True)
    Eq << apply(Add(Sum[k:1 + i:n](f(k)), f(i)))

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.dissect, cond={i})


if __name__ == '__main__':
    run()
