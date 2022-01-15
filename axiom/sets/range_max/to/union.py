from util import *


@apply
def apply(self, index=-1):
    a, b = self.of(Range)
    args = b.of(Max)
    former = Max(*args[:index])
    latter = Max(*args[index:])
    return Equal(self, Union(Range(a, former), Range(a, latter), evaluate=False))


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b, c = Symbol(integer=True)
    Eq << apply(Range(a, Max(b, c)))

    Eq << sets.eq.given.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el.imply.et.split.range), Eq[-1].this.rhs.apply(sets.el.given.et.split.range)

    Eq <<= Eq[-2].this.find(Less).apply(algebra.lt_max.imply.ou.lt), Eq[-1].this.find(Less).apply(algebra.lt_max.given.ou.lt)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.ou.split.union, simplify=None), Eq[-1].this.find(Element).apply(sets.el.imply.ou.split.union, simplify=None)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.et.split.range), Eq[-1].this.find(Element).apply(sets.el.imply.et.split.range)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el.given.et.split.range), Eq[-1].this.find(Element).apply(sets.el.imply.et.split.range)

    


if __name__ == '__main__':
    run()
# created on 2022-01-08
