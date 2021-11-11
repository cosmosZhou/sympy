from util import *



@apply(given=None)
def apply(self, cond=None):
    matched = []
    unmatch = []
    for eq in self.args:
        if eq.is_Or:
            if cond in eq.args:
                matched.append(Or(*eq._argset - {cond}))
                continue
        elif eq == cond:
            matched.append(S.false)
            continue
        unmatch.append(eq)
    assert unmatch
    return Equivalent(self, self.func(*unmatch, Or(cond, self.func(*matched))))


@prove
def prove(Eq):
    from axiom import algebra
    a, b, c, d = Symbol(integer=True, given=True)


    x, y = Symbol(real=True, given=True)

    f, g = Function(real=True)

    Eq << apply(((a < b) | (c < d)) & (f(x) < g(y)) & ((x < y) | (c < d)), cond=c < d)

    Eq << algebra.iff.given.et.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(algebra.et.imply.et.collect, cond=c < d)

    Eq << Eq[-1].this.lhs.apply(algebra.et.given.et.collect, cond=c < d)


if __name__ == '__main__':
    run()

# created on 2019-04-30
# updated on 2019-04-30
