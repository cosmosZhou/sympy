from util import *


@apply
def apply(le_add, factor=None):
    A, B = le_add.of(Arg + Arg < 2 * S.Pi / 3)
    if factor is not None:
        A *= factor
        B *= factor
    return Equal(((A * B) ** 3) ** (S.One / 3), A * B)


@prove
def prove(Eq):
    from axiom import algebra

    A = Symbol(complex=True, given=True)
    B = Symbol(complex=True, given=True)
    Eq << apply(Arg(A) + Arg(B) < 2 * S.Pi / 3)



if __name__ == '__main__':
    run()