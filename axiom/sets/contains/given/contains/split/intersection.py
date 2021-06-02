from util import *
import axiom



@apply
def apply(imply):
    e, AB = imply.of(Contains)

    return tuple(Contains(e, s) for s in AB.of(Intersection))

@prove
def prove(Eq):
    from axiom import sets
    x = Symbol.x(integer=True)
    A = Symbol.A(etype=dtype.integer)

    B = Symbol.B(etype=dtype.integer)

    Eq << apply(Contains(x, A & B))

    Eq << sets.contains.contains.imply.contains.intersection.apply(Eq[1], Eq[2])

if __name__ == '__main__':
    run()

