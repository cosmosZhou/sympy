from util import *


@apply
def apply(eq):
    args = eq.of(Equal)
    return LessEqual(*args)


@prove
def prove(Eq):
    a, b = Symbol(real=True)
    Eq << apply(Equal(a, b))

    Eq << Eq[1].subs(Eq[0])


if __name__ == '__main__':
    run()

from . import st
# created on 2019-04-22
# updated on 2019-04-22
