from util import *


@apply(given=None)
def apply(given, i=-1, j=None):
    [*args] = given.of(Or)
    if i < 0:
        i += len(args)
    if j is None:
        j = i - 1

    pivot = args[i]
    conj = pivot.invert()
    args[j] &= conj

    return Equivalent(given, Or(*args))

@prove
def prove(Eq):
    from axiom import algebra

    a, b, x, y = Symbol(real=True)
    Eq << apply(Greater(x, y) | Greater(a, b))



    Eq << Eq[-1].this.rhs.apply(algebra.ou.to.et)





if __name__ == '__main__':
    run()
# created on 2021-12-17
