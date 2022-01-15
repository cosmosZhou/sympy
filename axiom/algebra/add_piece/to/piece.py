from util import *


@apply
def apply(self):
    ecs, _ecs = self.of(Piecewise + Piecewise)

    rhs = add(ecs, _ecs)
    if rhs.is_Piecewise:
        from axiom.algebra.piece.flatten import flatten
        rhs = flatten(rhs)
        
    return Equal(self, rhs, evaluate=False)


def add(ecs, _ecs):
    piece = []
    u = S.true
    for e, c in ecs:
        args = []
        _u = S.true
        c_ = c & u
        for _e, _c in _ecs:
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
            piece.append((Piecewise(*args).simplify(), c))
        u &= c.invert()
    return Piecewise(*piece)


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
# created on 2018-02-23
