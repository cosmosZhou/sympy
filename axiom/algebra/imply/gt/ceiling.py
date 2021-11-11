from util import *

# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(x):
    return Greater(x, Ceiling(x) - 1)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)
    Eq << apply(x)

    Eq << algebra.imply.lt.ceiling.apply(x)

    Eq << Eq[-1].reversed

    Eq << Eq[-1] - 1


if __name__ == '__main__':
    run()

# created on 2018-10-28
# updated on 2018-10-28
