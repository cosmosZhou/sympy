from util import *


@apply(given=None)
def apply(eq):
    a, b = eq.of(Equal)
    return Equivalent(eq, Equal(b, a), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    b, a = Symbol(real=True, given=True)
    Eq << apply(Equal(a, b))

    Eq << algebra.iff.given.et.infer.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-04-19
