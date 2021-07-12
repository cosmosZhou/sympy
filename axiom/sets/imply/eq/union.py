from util import *


@apply
def apply(A, B):
    return Equal(A, Union(A & B, A - B, evaluate=False), evaluate=False)


@prove
def prove(Eq):
    from axiom import sets

    A = Symbol.A(etype=dtype.integer)
    B = Symbol.B(etype=dtype.integer)
    Eq << apply(A, B)

    C = Symbol.C(A - B)
    Eq << C.this.definition

    Eq << sets.eq.imply.eq.union.apply(Eq[1], A & B)

    Eq << Eq[0].subs(Eq[1].reversed).reversed


if __name__ == '__main__':
    run()