from util import *


@apply
def apply(gt):
    x, a = gt.of(Greater)
    return Less(a, x)


@prove
def prove(Eq):
    from axiom import algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(x > a)

    Eq << algebra.lt.imply.gt.reverse.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2019-07-17
