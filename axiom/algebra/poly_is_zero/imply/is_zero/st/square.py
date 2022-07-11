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

    Eq << algebra.ne_zero.imply.gt_zero.abs.apply(Eq[-1])

    Eq << algebra.gt_zero.imply.gt_zero.square.apply(Eq[-1])

    Eq << algebra.imply.ge_zero.square.apply(y)

    Eq << algebra.imply.ge_zero.square.apply(z)

    Eq << algebra.ge_zero.ge_zero.imply.ge_zero.add.apply(Eq[-1], Eq[-2])

    Eq << algebra.ge_zero.gt_zero.imply.gt_zero.add.apply(Eq[-1], Eq[-4])

    Eq << Eq[-1].subs(Eq[0])




if __name__ == '__main__':
    run()
# created on 2018-06-08
# updated on 2022-01-07