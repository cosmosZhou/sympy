from util import *


@apply(given=None)
def apply(self):
    q, p = self.of(Necessary)
    return Equivalent(self, Necessary(p.invert(), q.invert()))


@prove
def prove(Eq):
    from axiom import algebra
    
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)
    Eq << apply(Necessary(x > y, f(x) > g(y)))
    
    Eq << Eq[0].this.lhs.apply(algebra.necessary.to.ou)
    
    Eq << Eq[-1].this.rhs.apply(algebra.necessary.to.ou)


if __name__ == '__main__':
    run()