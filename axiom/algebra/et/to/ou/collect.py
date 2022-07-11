from util import *


@apply(given=None)
def apply(self, *, cond=None):
    cond=sympify(cond)

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
    assert not unmatch
    return Equivalent(self, Or(cond, self.func(*matched)))


@prove
def prove(Eq):
    from axiom import algebra

    p, q, r, s = Symbol(bool=True)
    Eq << apply(And(q | p, r | p, s | p), cond=p)

    Eq << algebra.iff.given.et.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(algebra.et.imply.ou.collect, cond=p)

    Eq << Eq[-1].this.lhs.apply(algebra.et.given.ou.collect, cond=p)

    


if __name__ == '__main__':
    run()
# created on 2022-01-28
