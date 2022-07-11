from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Interval)
    kwargs = self.kwargs
    args = a.of(Min)
    former = Min(*args[:index])
    latter = Min(*args[index:])
    return Equal(self, Union(Interval(former, b, **kwargs), Interval(latter, b, **kwargs), evaluate=False))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Interval(Min(b, c), a, right_open=True))

    Eq << sets.eq.given.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_interval.imply.et), Eq[-1].this.rhs.apply(sets.el_interval.given.et)

    Eq <<= Eq[-2].this.find(GreaterEqual).apply(algebra.ge_min.imply.ou.ge), Eq[-1].this.find(GreaterEqual).apply(algebra.ge_min.given.ou.ge)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_union.given.ou, simplify=None), Eq[-1].this.find(Element).apply(sets.el_union.imply.ou, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_interval.given.et), Eq[-1].this.find(Element).apply(sets.el_interval.imply.et)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_interval.given.et), Eq[-1].this.find(Element).apply(sets.el_interval.imply.et)




if __name__ == '__main__':
    run()
# created on 2022-01-08
