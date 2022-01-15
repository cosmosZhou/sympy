from util import *


@apply(given=None)
def apply(given, i=-1, j=None, *, simplify=True):
    [*args] = given.of(And)
    if i < 0:
        i += len(args)
    if j is None:
        j = i - 1

    pivot = args[i]
    conj = pivot.invert()
    args[j] |= conj
    if simplify:
        args[j] = args[j].simplify()
            
    imply = And(*args)
    if simplify:
        imply = imply.simplify()
    return Equivalent(given, imply, evaluate=False)

@prove
def prove(Eq):
    from axiom import algebra

    a, b, x, y = Symbol(real=True)
    Eq << apply(Greater(x, y) & Greater(a, b))

    Eq << Eq[-1].this.rhs.apply(algebra.et.to.ou)

    


if __name__ == '__main__':
    run()
# created on 2021-12-17
# updated on 2022-01-02