from util import *


@apply
def apply(equal, contains):
    if contains.is_Equal:
        contains, equal = equal, contains

    a, A = contains.of(Element)

    complement_A_a, complement_B_a = equal.of(Equal)
    _A, _a = complement_A_a.of(Complement)
    _a = _a.of(FiniteSet)

    assert a == _a
    B, _a = complement_B_a.of(Complement)
    _a = _a.of(FiniteSet)

    assert a == _a

    if A != _A:
        _A, B = B, _A
    assert A == _A

    return Equal(A, B | a.set)


@prove
def prove(Eq):
    from axiom import sets

    A, B = Symbol(etype=dtype.integer, given=True)
    a = Symbol(integer=True, given=True)
    Eq << apply(Equal(A - a.set, B - a.set), Element(a, A))

    Eq << sets.eq.imply.eq.union.apply(Eq[0], a.set)

    Eq << sets.el.imply.eq.union.apply(Eq[1])

    Eq << Eq[-2].this.lhs.subs(Eq[-1])


if __name__ == '__main__':
    run()


from . import finiteset
# created on 2021-03-27
