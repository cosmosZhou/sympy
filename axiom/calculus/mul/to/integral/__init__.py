from util import *


@apply
def apply(self): 
    for i, sgm in enumerate(self.args):
        if isinstance(sgm, Integral):
            args = [*self.args]
            args[i] = S.One
            variables_set = sgm.variables_set
            duplicate_set = set()
            for a in args:
                duplicates = {v for v in variables_set if a._has(v)}
                if duplicates:
                    variables_set -= duplicates
                    duplicate_set |= duplicates
            
            if duplicate_set:
                excludes = set()
                for v in duplicate_set:
                    _v = self.generate_var(excludes=excludes, **v.type.dict)
                    sgm = sgm.limits_subs(v, _v)
                    excludes.add(_v)                        
                    
            args[i] = sgm.function
            function = self.func(*args).powsimp()
            return Equal(self, Integral(function, *sgm.limits))


@prove
def prove(Eq):
    x = Symbol.x(real=True)
    y = Symbol.y(real=True)
    a = Symbol.a(real=True)
    b = Symbol.b(real=True)
    c = Symbol.c(real=True)
    d = Symbol.d(real=True)
    f = Function.f(real=True)
    Eq << apply(Integral[x:a:b](f(x)) * y)

    Eq << Eq[-1].this.rhs.simplify()


if __name__ == '__main__':
    run()

from . import as_multiple_limits