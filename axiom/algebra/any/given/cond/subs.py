from util import *


@apply
def apply(self, old, new):
    assert not old.is_given
    exists = self.limits_dict        
    if old in exists:
        domain = exists[old]
        if not domain:
            domain = old.domain
        eqs = []

        if not isinstance(domain, list):
            if not domain.is_set:
                domain = old.domain_conditioned(domain)
            if new.is_symbol:
                _eval_domain_defined = self.expr.domain_defined(new)
                if _eval_domain_defined in domain:
                    ...
                else:
                    eqs.append(Contains(new, domain))
            else:
                eqs.append(Contains(new, domain))

        if self.expr.is_And:
            for equation in self.expr.args:
                eqs.append(equation.subs(old, new))
        else:
            eqs.append(self.expr._subs(old, new))
            
        assert not self.limits_delete(old)
        
        if new.is_symbol and new.definition is None and not new.is_given:
            return

        return And(*eqs)
        
    if old.is_Slice:
        from axiom.algebra.slice.to.matrix import convert   
        old = convert(old)
        if old.is_DenseMatrix:
            old = Tuple(*old._args)                    
            if old in exists or all(sym in exists for sym in old):
                ...
            else:
                return 

    if old.is_Tuple and all(sym in exists for sym in old): 
        domains = [exists[sym] for sym in old]
        eqs = []

        for domain in domains:
            if not isinstance(domain, list):
                if not domain.is_set:
                    domain = old.domain_conditioned(domain)                    
                eqs.append(Contains(new, domain))

        if self.expr.is_And:
            for equation in self.expr.args:
                eqs.append(equation._subs(old, new))
        else:
            if old.is_Tuple:
                function = self.expr
                for i in range(len(old)):
                    function = function._subs(old[i], new[i])
                eqs.append(function)
            else:
                eqs.append(self.expr._subs(old, new))
                
        assert not self.limits_delete(old)
        assert not new.is_symbol
        return And(*eqs)


@prove
def prove(Eq):
    e = Symbol.e(real=True, given=True)
    x = Symbol.x(integer=True)
    f = Function.f(shape=(), integer=True)
    g = Function.g(shape=(), integer=True)
    Eq << apply(Any[x](x > g(x)), x, f(e))

    Eq << ~Eq[0]

    Eq << Eq[-1].simplify()

    Eq << Eq[-1].subs(x, f(e))

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()