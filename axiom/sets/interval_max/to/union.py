from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Interval)
    kwargs = self.kwargs
    args = b.of(Max)
    former = Max(*args[:index])
    latter = Max(*args[index:])
    return Equal(self, Union(Interval(a, former, **kwargs), Interval(a, latter, **kwargs), evaluate=False))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Interval(a, Max(b, c), left_open=True, right_open=True))

    Eq << sets.eq.given.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el.imply.et.split.interval), Eq[-1].this.rhs.apply(sets.el.given.et.split.interval)

    Eq <<= Eq[-2].this.find(Less).apply(algebra.lt_max.imply.ou.lt), Eq[-1].this.find(Less).apply(algebra.lt_max.given.ou.lt)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.ou.split.union, simplify=None), Eq[-1].this.find(Element).apply(sets.el.imply.ou.split.union, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.et.split.interval), Eq[-1].this.find(Element).apply(sets.el.imply.et.split.interval)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.et.split.interval), Eq[-1].this.find(Element).apply(sets.el.imply.et.split.interval)

    


if __name__ == '__main__':
    run()
# created on 2022-01-08
