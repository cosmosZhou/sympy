from util import *


@apply(given=None)
def apply(given, index=-1):
    e, args = given.of(Element[Intersection])
    first = Intersection(*args[:index])
    second = Intersection(*args[index:])
    return Equivalent(given, And(Element(e, first), Element(e, second)), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra, sets

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A & B))

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_intersect.imply.et), Eq[-1].this.rhs.apply(sets.el.el.imply.el.intersect)




if __name__ == '__main__':
    run()
# created on 2022-01-01

