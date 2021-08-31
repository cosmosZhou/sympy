from util import *


@apply(given=None)
def apply(given, B):
    x, A = given.of(Element)

    return Equivalent(given, Or(Element(x, A - B), Element(x, A & B)))


@prove
def prove(Eq):
    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)
    Eq << apply(Element(x, A), B)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()


from . import finiteset, union
