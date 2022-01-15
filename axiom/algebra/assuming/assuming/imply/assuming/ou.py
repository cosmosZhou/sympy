from util import *



@apply
def apply(x_imply_P, y_imply_P):
    p, x = x_imply_P.of(Assuming)
    q, y = y_imply_P.of(Assuming)

    return Assuming(p | q, x | y)


@prove
def prove(Eq):
    from axiom import algebra
    x, y, a, b = Symbol(real=True, given=True)

    Eq << apply(Assuming(a > 0, x > 0), Assuming(b > 0, y > 0))

    Eq << Eq[2].reversed

    Eq << algebra.infer.infer.imply.infer.ou.apply(Eq[0].reversed, Eq[1].reversed)


if __name__ == '__main__':
    run()
# created on 2019-02-08
