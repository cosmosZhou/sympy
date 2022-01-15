from util import *

# P is condition set;


@apply
def apply(y, x=None):
    U = y.universalSet

    if x is None:
        x = y.generate_var(**y.type.dict)
    return All[x:U - y.set](Unequal(x, y))


@prove
def prove(Eq):
    from axiom import algebra
    y = Symbol(complex=True)
    Eq << apply(y)

    Eq << algebra.all.given.ou.apply(Eq[0])

if __name__ == '__main__':
    run()

# created on 2021-04-21
