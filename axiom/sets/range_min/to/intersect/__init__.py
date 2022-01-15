from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Range)
    args = b.of(Min)
    former = Min(*args[:index])
    latter = Min(*args[index:])
    return Equal(self, Intersection(Range(a, former), Range(a, latter), evaluate=False))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Range(a, Min(b, c)))

    Eq << sets.eq.given.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el.imply.et.split.range), Eq[-1].this.rhs.apply(sets.el.given.et.split.range)

    Eq <<= Eq[-2].this.find(Less).apply(algebra.lt_min.imply.et.lt), Eq[-1].this.find(Less).apply(algebra.lt_min.given.et.lt)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.et.split.intersect, simplify=None), Eq[-1].this.find(Element).apply(sets.el.imply.et.split.intersect, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.et.split.range), Eq[-1].this.find(Element).apply(sets.el.imply.et.split.range)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.et.split.range), Eq[-1].this.find(Element).apply(sets.el.imply.et.split.range)




if __name__ == '__main__':
    run()
# created on 2022-01-01

