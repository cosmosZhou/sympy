from util import *


@apply
def apply(given, *, cond=None):
    from axiom.algebra.ou.imply.ou.collect import collect
    return collect(given, cond)


@prove
def prove(Eq):
    from axiom import algebra

    x, y = Symbol(real=True, given=True)
    f, h, g = Function(real=True)
    Eq << apply(Unequal(x, y) | Equal(f(x), g(y)) & (y > 0) | Equal(h(x), g(y)) & (y > 0), cond=y > 0)

    Eq << Eq[1].this.args[0].apply(algebra.et.imply.ou, simplify=None)


if __name__ == '__main__':
    run()
# created on 2018-02-22
