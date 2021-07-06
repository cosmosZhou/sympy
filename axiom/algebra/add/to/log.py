from util import *


@apply
def apply(self):
    args = self.of(Add)
    
    logs = []
    for arg in args:
        if arg.is_Log:
            logs.append(arg.arg)
        else:            
            [*_args] = arg.of(Mul)
            log_x = None
            for i, log_x in enumerate(_args):
                if log_x.is_Log:
                    break
            else:
                return
            del _args[i]
            coeff = Mul(*_args)
            assert coeff.is_odd
            logs.append(log_x.arg ** coeff)

    rhs = log(Mul(*logs), evaluate=False)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    Eq << apply(Log(a) - Log(b))

    Eq << algebra.eq.given.eq.exp.apply(Eq[-1])


if __name__ == '__main__':
    run()