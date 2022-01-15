from util import *


@apply(given=False)
def apply(self, index=-1):
    [*args] = self.of(And)
    factor = args.pop(index)

    for i, ou in enumerate(args):
        if ou.is_Or:
            args[i] = Or(*(arg & factor for arg in ou.args))
            return Equivalent(self, And(*args))


@prove
def prove(Eq):
    from axiom import algebra

    a, b, c, d, e, f, x, y = Symbol(real=True)
    Eq << apply(((a < b) | (e < f)) & (c < d) & (x < y))

    Eq << Eq[0].this.find(Or[And]).apply(algebra.ou.collect, cond=x < y)





if __name__ == '__main__':
    run()
# created on 2021-12-17
