from util import *


@apply(given=None)
def apply(given, index=None):
    x, intersection = given.of(Contains)

    ss = intersection.of(Intersection)
    if index is None:
        et = [Contains(x, s) for s in ss]
    else:
        ss = ss[index]
        if isinstance(index, slice):
            et = [Contains(x, s) for s in ss]
            et.append(given)
        else:
            et = [Contains(x, ss), given]
    return Equivalent(given, And(*et))


@prove
def prove(Eq):
    from axiom import sets, algebra
    x = Symbol.x(real=True)
    A = Symbol.A(etype=dtype.real)
    B = Symbol.B(etype=dtype.real)

    Eq << apply(Contains(x, A & B), index=0)

    Eq << algebra.equivalent.given.suffice.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.contains.imply.contains.split.intersection)


if __name__ == '__main__':
    run()

