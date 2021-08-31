from util import *


def extract(cls, self):
    for i, arg in enumerate(self.of(Mul)):
        if not isinstance(arg, cls):
            continue

        args = [*self.args]
        del args[i]

        rest = self.func(*args)
        if rest.is_extended_positive:
            return cls(*(e * rest for e in arg.args))

    for i, arg in enumerate(self.args):
        if not isinstance(arg, cls.negated_type):
            continue
        args = [*self.args]
        del args[i]

        rest = self.func(*args)
        if rest.is_extended_negative:
            return cls(*(e * rest for e in arg.args))

@apply
def apply(self, evaluate=False):
    rhs = extract(Min, self)

    return Equal(self, rhs, evaluate=evaluate)


@prove
def prove(Eq):
    from axiom import algebra

    t = Symbol(real=True, positive=True)
    x, y = Symbol(real=True)
    Eq << apply(t * Min(x, y))
    Eq << Eq[0].this.rhs.apply(algebra.min.to.mul)


if __name__ == '__main__':
    run()
