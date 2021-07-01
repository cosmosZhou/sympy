



from util import *
# given : {e} ∩ s = a, |a| > 0 => e ∈ s


@apply
def apply(e, s):
    return Equal(s & e.set, Piecewise((e.set, Contains(e, s)), (e.emptySet, True)))




@prove
def prove(Eq):
    s = Symbol.s(etype=dtype.integer)
    e = Symbol.e(integer=True)
    
    Eq << apply(e, s)
    
    Eq << Eq[-1].this.rhs.simplify()    
    

if __name__ == '__main__':
    run()

