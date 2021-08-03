from util import *


@apply
def apply(given, index=0):
    args = []
    for arg in given.of(Equal[Add, 0]):
        arg = arg.of(Expr ** 2)
        assert arg.is_extended_real
        args.append(arg)
    
    return Equal(args[index], 0)


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Equal(x * x + y * y + z * z, 0))

    Eq << ~Eq[1]

    Eq << algebra.is_nonzero.imply.abs_is_positive.apply(Eq[-1])

    Eq << algebra.is_positive.imply.is_positive.square.apply(Eq[-1])

    Eq << algebra.imply.is_nonnegative.square.apply(y)

    Eq << algebra.imply.is_nonnegative.square.apply(z)

    Eq << algebra.is_nonnegative.is_nonnegative.imply.is_nonnegative.add.apply(Eq[-1], Eq[-2])

    Eq << algebra.is_nonnegative.is_positive.imply.is_positive.add.apply(Eq[-1], Eq[-4])

    Eq << Eq[-1].subs(Eq[0])


if __name__ == '__main__':
    run()