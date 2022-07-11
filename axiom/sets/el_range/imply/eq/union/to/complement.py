from util import *


@apply
def apply(el):
    i, (a, b) = el.of(Element[Range])
    a += 1
    b -= 1
    return Equal(Range(a, i) | Range(i + 1, b), Range(a, b) - {i})


@prove
def prove(Eq):
    from axiom import sets, algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(Element(i, Range(-1, n + 1)))

    Eq << sets.eq.given.et.infer.apply(Eq[1])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_union.imply.ou), Eq[-1].this.rhs.apply(sets.el_union.given.ou)

    Eq <<= Eq[-2].this.rhs.apply(sets.el_complement.given.et, simplify=False), Eq[-1].this.lhs.apply(sets.el_complement.imply.et)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_range.to.et), Eq[-1].this.find(Element).apply(sets.el_range.to.et)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_range.to.et), Eq[-1].this.find(Element).apply(sets.el_range.to.et)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_range.to.et), Eq[-1].this.find(Element).apply(sets.el_range.to.et)

    Eq << Eq[-1].this.rhs.find(GreaterEqual).apply(algebra.ge.to.gt.strengthen)

    Eq << Eq[-2].this.find(NotElement).simplify()

    Eq << Eq[-1].this.find(Symbol >= Add).apply(algebra.ge.to.gt.strengthen)

    Eq << algebra.infer.given.et.infer.split.ou.apply(Eq[-1])

    Eq <<= algebra.infer.given.et.infer.apply(Eq[-2]), algebra.infer.given.et.infer.apply(Eq[-1])

    Eq <<= algebra.infer_et.given.infer.delete.apply(Eq[-4]), algebra.infer_et.given.infer.delete.apply(Eq[-3]), algebra.infer_et.given.infer.delete.apply(Eq[-2], 0), algebra.infer_et.given.infer.delete.apply(Eq[-1], 0)

    Eq <<= algebra.infer.given.ou.apply(Eq[-4]), algebra.infer.given.ou.apply(Eq[-3]), algebra.infer.given.ou.apply(Eq[-2]), algebra.infer.given.ou.apply(Eq[-1])

    Eq <<= sets.ou.given.notin.range.apply(Eq[-2]), sets.ou.given.notin.range.apply(Eq[-1])

    Eq <<= sets.notin.given.is_empty.apply(Eq[-2]), sets.notin.given.is_empty.apply(Eq[-1])

    Eq << sets.el_range.imply.et.apply(Eq[0])

    Eq << sets.ge.imply.range_is_empty.apply(Eq[-2] + 1)

    Eq << algebra.lt.imply.le.strengthen.apply(Eq[-1])

    Eq << sets.le.imply.range_is_empty.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2022-01-28
