from util import *


@apply(given=None)
def apply(self):
    p, q = self.of(Infer)
    return Equivalent(self, p.invert() | q, evaluate=False)


@prove(provable=False)
def prove(Eq):
    p, q = Symbol(bool=True)
    Eq << apply(Infer(p, q))

    


if __name__ == '__main__':
    run()
# created on 2018-01-01
# updated on 2022-01-27
