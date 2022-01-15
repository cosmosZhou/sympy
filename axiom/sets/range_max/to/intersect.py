from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Range)
    args = a.of(Max)
    former = Max(*args[:index])
    latter = Max(*args[index:])
    return Equal(self, Intersection(Range(former, b), Range(latter, b), evaluate=False))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Range(Max(b, c), a))

    Eq << sets.eq.given.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el.imply.et.split.range), Eq[-1].this.rhs.apply(sets.el.given.et.split.range)

    Eq <<= Eq[-2].this.find(GreaterEqual).apply(algebra.ge_max.imply.et.ge), Eq[-1].this.find(GreaterEqual).apply(algebra.ge_max.given.et.ge)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.et.split.intersect, simplify=None), Eq[-1].this.find(Element).apply(sets.el.imply.et.split.intersect, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.et.split.range), Eq[-1].this.find(Element).apply(sets.el.imply.et.split.range)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.et.split.range), Eq[-1].this.find(Element).apply(sets.el.imply.et.split.range)

    


if __name__ == '__main__':
    run()
# created on 2022-01-08
