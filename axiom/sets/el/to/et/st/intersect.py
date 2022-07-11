from util import *


@apply(given=None)
def apply(given, index=None):
    x, intersection = given.of(Element)

    ss = intersection.of(Intersection)
    if index is None:
        et = [Element(x, s) for s in ss]
    else:
        ss = ss[index]
        if isinstance(index, slice):
            et = [Element(x, s) for s in ss]
            et.append(given)
        else:
            et = [Element(x, ss), given]
    return Equivalent(given, And(*et))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)

    Eq << apply(Element(x, A & B), index=0)

    Eq << algebra.iff.given.et.infer.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.el_intersect.imply.el)


if __name__ == '__main__':
    run()

# created on 2019-10-08
