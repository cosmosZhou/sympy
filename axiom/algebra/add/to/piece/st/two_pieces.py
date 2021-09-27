from util import *


@apply
def apply(self):
    piece0, piece1 = self.of(Add)

    assert piece0.is_Piecewise
    assert piece1.is_Piecewise

    from axiom.algebra.piece.flatten import flatten
    return Equal(self, flatten(add(piece0, piece1)))


def add(self, other):
    piece = []
    u = S.true
    for e, c in self.args:
        args = []
        _u = S.true
        c_ = c & u
        for _e, _c in other.args:
            _c_ = _c & _u
            _c_ = c_ & _c_
            if _c_.is_BooleanFalse:
                continue
            args.append([(e + _e).simplify(), _c])
            _u &= _c.invert()
        if len(args) == 1:
            piece.append((args[-1][0], c))
        else:
            args[-1][-1] = True
            piece.append((self.func(*args).simplify(), c))
        u &= c.invert()
    return self.func(*piece)


@prove
def prove(Eq):
    from axiom import algebra
    x = Symbol(real=True)
    A, B = Symbol(etype=dtype.real)

    f, g, h, p = Function(real=True)
    Eq << apply(Piecewise((f(x), Element(x, A)), (g(x), True)) + Piecewise((h(x), Element(x, B)), (p(x), True)))

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.piece)

    Eq << Eq[-1].this.find(Add).apply(algebra.add.to.piece)

    Eq << Eq[-1].this.lhs.args[1].find(Add).apply(algebra.add.to.piece)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.flatten)


if __name__ == '__main__':
    run()
