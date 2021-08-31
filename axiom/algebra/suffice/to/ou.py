from util import *


@apply(given=None)
def apply(self):
    p, q = self.of(Suffice)
    return Equivalent(self, p.invert() | q, evaluate=False)


@prove(provable=False)
def prove(Eq):
    x, y = Symbol(integer=True)
    f, g = Function(integer=True)

    Eq << apply(Suffice(x > y, f(x) > g(y)))

if __name__ == '__main__':
    run()
