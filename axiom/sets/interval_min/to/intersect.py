from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Interval)
    kwargs = self.kwargs
    args = b.of(Min)
    former = Min(*args[:index])
    latter = Min(*args[index:])
    return Equal(self, Intersection(Interval(a, former, **kwargs), Interval(a, latter, **kwargs), evaluate=False))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Interval(a, Min(b, c), left_open=True))

    Eq << sets.eq.given.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_interval.imply.et), Eq[-1].this.rhs.apply(sets.el_interval.given.et)

    Eq <<= Eq[-2].this.find(LessEqual).apply(algebra.le_min.imply.et.le), Eq[-1].this.find(LessEqual).apply(algebra.le_min.given.et.le)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_intersect.given.et, simplify=None), Eq[-1].this.find(Element).apply(sets.el_intersect.imply.et, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_interval.given.et), Eq[-1].this.find(Element).apply(sets.el_interval.imply.et)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_interval.given.et), Eq[-1].this.find(Element).apply(sets.el_interval.imply.et)




if __name__ == '__main__':
    run()
# created on 2022-01-08
