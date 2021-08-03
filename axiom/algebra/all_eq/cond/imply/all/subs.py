from util import *


def subs(self, old, new, simplify=True, assumptions={}):
    if self == old:
        return new
    
    if self.is_Add and old.is_Add:
        this = self._eval_subs(old, new, simplify=simplify, assumptions=assumptions)
        if this is not None:
            return this
        
    if self.is_Mul and old.is_Mul:
        this = self._eval_subs(old, new, simplify=simplify, assumptions=assumptions)
        if this is not None:
            return this
        
    if self.is_ExprWithLimits:
        for x, *ab in self.limits:
            if old._has(x):
                domain = assumptions.get(x)
                if domain is False:
                    return self
                
        limits = [*self.limits]
        hit = False
        for i, [x, *ab] in enumerate(limits):
            _ab = [subs(c, old, new, simplify=simplify, assumptions=assumptions) for c in ab]
            if _ab != ab:                    
                limits[i] = (x, *_ab)
                hit = True
        
        expr = subs(self.expr, old, new, simplify=simplify, assumptions=assumptions)
        hit |= expr != self.expr
        
        if hit:
            self = self.func(expr, *limits)
            if simplify:
                self = self.simplify()
        return self
    
    hit = False
    args = [*self.args]
    for i, arg in enumerate(args):
        _arg = subs(arg, old, new, simplify=simplify, assumptions=assumptions)
        if _arg != arg:
            hit = True
            args[i] = _arg
    if hit:
        return self.func(*args, **self.kwargs)
    return self
    

@apply
def apply(*given, reverse=False, simplify=True, assumptions={}):
    eq, f_eq = given
    assert not f_eq.is_Quantifier
    (lhs, rhs), *limits = eq.of(All[Equal])
    if reverse:
        lhs, rhs = rhs, lhs
    return All(subs(f_eq, lhs, rhs, simplify=simplify, assumptions=assumptions), *limits)


@prove
def prove(Eq):
    from axiom import algebra

    m = Symbol.m(integer=True, positive=True)
    n = Symbol.n(integer=True, positive=True)
    a = Symbol.a(real=True, shape=(m, n))
    b = Symbol.b(real=True, shape=(m, n))
    c = Symbol.c(real=True, shape=(m, n))
    f = Function.f(real=True)
    C = Symbol.C(etype=dtype.real * (m, n))
    S = Symbol.S(etype=dtype.real * (m, n))
    Eq << apply(All[c:C](Equal(a, f(c))), Contains(a * b + c, S))

    Eq << algebra.cond.all.imply.all_et.apply(Eq[1], Eq[0])

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs)


if __name__ == '__main__':
    run()
