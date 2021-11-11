from util import *


@apply(given=None)
def apply(gt):
    x, a = gt.of(Greater)
    return Equivalent(gt, Less(a, x), evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(x > a)

    Eq << algebra.iff.given.et.infer.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2019-08-02
# updated on 2019-08-02
