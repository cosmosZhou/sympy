from util import *


def collect(self, *factors):
    args = self.of(Add)
    additives = []
    others = []    
    factor, *factors = factors
    for arg in args:
        if arg._has(factor):
            additives.append(arg / factor)
        elif arg._has(-factor):
            additives.append(-(arg / -factor))
        else:
            others.append(arg)
    
    sgm = Add(*additives)
    if factors:
        sgm = collect(sgm, *factors)
    
    sgm *= factor
    if others:
        sgm += Add(*others)
    
    return sgm

@apply
def apply(self, factor=None):
    args = self.of(Add)
    common_terms = None
    others = []
    
    additives = []
    if factor is None:
        muls = []
        for arg in args:
            if arg.is_Mul:
                if common_terms is None:
                    common_terms = {*arg.args}
                else:
                    if common_terms & {*arg.args}:                            
                        common_terms &= {*arg.args}
                    else:
                        others.append(arg)
                        continue
                muls.append(arg)
            else:
                others.append(arg)
    
        for arg in muls:        
            arg = Mul(*{*arg.args} - common_terms)
            additives.append(arg)
            
        rhs = Add(*additives) * Mul(*common_terms) + Add(*others)
    else:
        if factor.is_Mul:
            rhs = collect(self, *factor.args)
        else:
            rhs = collect(self, factor)
        
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from axiom import algebra

    a = Symbol.a(complex=True)
    b = Symbol.b(complex=True)
    x = Symbol.x(complex=True)
    y = Symbol.y(complex=True)
    Eq << apply(a * x - a * y + b + b * y, factor=b)

    Eq << Eq[0].this.find(Mul[Add]).apply(algebra.mul.to.add)


if __name__ == '__main__':
    run()