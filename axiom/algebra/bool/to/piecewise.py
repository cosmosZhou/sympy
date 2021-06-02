from util import *


@apply
def apply(self):
    assert self.is_Bool
    return Equal(self, Piecewise((1, self.arg), (0, True)))


@prove(provable=False)
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
     
    Eq << apply(Bool(x > y))
    return
    Eq << algebra.eq.given.ou.apply(Eq[0])
    
    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=0)
    
    Eq << Eq[-1].this.args[0].apply(algebra.et.given.et.subs.bool, index=0, invert=True)
    

if __name__ == '__main__':
    run()

