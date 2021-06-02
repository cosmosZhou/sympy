from util import *


def rewrite_from_MinMaxBase(self, common_terms=None):
    if common_terms is None:
    
        for plus in self.args:
            if isinstance(plus, Add):
                if common_terms is None:
                    common_terms = {*plus.args}
                else:
                    common_terms &= {*plus.args}
            else:
                if common_terms is None:
                    common_terms = {plus}
                else:
                    common_terms &= {plus}
        if common_terms:
            args = []
            for e in self.args:
                if isinstance(e, Add):
                    e = Add(*{*e.args} - common_terms)
                elif e.is_Zero:
                    ...
                else:
                    e = 0
                args.append(e)
            return Add(*common_terms, self.func(*args))
    else:
        return Add(common_terms, self.func(*(plus - common_terms for plus in self.args)))


@apply
def apply(self, common_term=None): 
    assert self.is_Min
    
    return Equal(self, rewrite_from_MinMaxBase(self, common_term))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    r = Symbol.r(real=True, positive=True)
    
    Eq << apply(Min(x * r + 1, y * r + 1))
    
    Eq << Eq[-1].this.lhs.astype(Piecewise)
    
    Eq << Eq[-1].this.lhs.astype(Add)
    
    Eq << Eq[-1].this.rhs.astype(Piecewise)
    
    
if __name__ == '__main__':
    run()
    
