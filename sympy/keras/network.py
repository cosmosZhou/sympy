from _functools import reduce

class NetWorkMetaClass(type):
    
    mapping = {}
    
    def __init__(cls, *args, **kws):
        NetWorkMetaClass.mapping[cls.__name__[7:]] = cls
        
        
class NetWork(metaclass=NetWorkMetaClass):
    
    def __new__(cls, *args):
        self = object.__new__(cls)
        self.args, self.indices = zip(*args)
        return self
            
    def prepare(self, **kwargs):
        backend, = kwargs
        for arg in self.args:
            if isinstance(arg, NetWork):
                arg.prepare(**kwargs)
            elif isinstance(arg, tuple):
                for arg in arg:
                    if isinstance(arg, NetWork):
                        arg.prepare(**kwargs)
                    else:
                        getattr(arg, backend)
            else:
                getattr(arg, backend)

    def __call__(self, *args, **kwargs):
        backend, = kwargs
        raise Exception('unresolved cases')
    
    def forward(self, *args, **kwargs):
        return tuple(arg(*args, **kwargs) if isinstance(arg, NetWork) else getattr(arg, backend) for arg in self.args)

class NetWorkSymbol(NetWork):
    
    def __new__(cls, sym):
        self = object.__new__(cls)
        self.sym = sym
        self.args = ()
        return self
        
    def __call__(self, *args, **kwargs):
        backend, = kwargs
        if len(args) != 1:
            return args[0]
        else:
            sym, = args
            return sym
    

class NetWorkAppliedUndef(NetWork):
    
    def __new__(cls, expr, *args):
        self = NetWork.__new__(cls, *args)
        self.expr = expr
        return self
        
    def __call__(self, *args, **kwargs):
        args = self.forward(*args, **kwargs)
        return self.expr._execute_torch_recursion(*args)

        
class NetWorkIndexed(NetWork):
    
    def __call__(self, *args, **kwargs):
        base, *indices = self.forward(*args, **kwargs)
        return base[indices]
    
    
class NetWorkPiecewise(NetWork):
    
    def __call__(self, *args, **kwargs):
        backend, = kwargs
        for e, c in self.args:
            c = c(*args, **kwargs) if isinstance(c, NetWork) else getattr(c, backend)
            e = e(*args, **kwargs) if isinstance(e, NetWork) else getattr(e, backend)
            
            if c == True:
                return e
        
        
class NetWorkReducedArgMax(NetWork):

    def __call__(self, *args, **kwargs):
        backend, = kwargs
        arg, = self.forward(*args, **kwargs)
        if backend == 'torch':
            return arg.argmax(-1)
        if backend == 'tensorflow':
            import tensorflow as tf
            return tf.argmax(arg, -1)


class NetWorkTuple(NetWork):
    
    def __call__(self, *args, **kwargs):
        return self.forward(*args, **kwargs)
    
    
class NetWorkExprCondPair(NetWork):
    
    def __call__(self, *args, **kwargs):
        return self.forward(*args, **kwargs)
    
    
class NetWorkAdd(NetWork):
    
    def __call__(self, *args, **kwargs):
        return sum(self.forward(*args, **kwargs))
        
        
class NetWorkMul(NetWork):
    
    def __call__(self, *args, **kwargs):
        return reduce(lambda a, b: a * b, self.forward(*args, **kwargs))
                
                
class NetWorkMatMul(NetWork):
    
    def __call__(self, *args, **kwargs):
        backend, = kwargs
        return reduce(lambda x, y: x @ y if len(y.shape) > 1 else (x @ y.unsqueeze(-1)).squeeze(-1), self.forward(*args, **kwargs))
                

class NetWorkLamda(NetWork):

    def __call__(self, *args, **kwargs):
        backend, = kwargs
        expr, *shape = self.args

        shape = [arg(*args, **kwargs) if isinstance(arg, NetWork) else getattr(arg, backend) for arg in shape]
        
        import itertools
        results = [expr(*vars, *args, **kwargs) for vars in itertools.product(*(range(size) for size in shape))] \
        if isinstance(expr, NetWork) else \
        [getattr(expr, backend)] * reduce(lambda a, b: a * b, shape)
        
        import torch
        return torch.stack(results).reshape(shape, *expr.shape)


class NetWorkLess(NetWork):

    def __call__(self, *args, **kwargs):
        lhs, rhs = self.forward(*args, **kwargs)
        return lhs < rhs


class NetWorkGreater(NetWork):
                    
    def __call__(self, *args, **kwargs):
        lhs, rhs = self.forward(*args, **kwargs)
        return lhs > rhs


class NetWorkLessEqual(NetWork):
                    
    def __call__(self, *args, **kwargs):
        lhs, rhs = self.forward(*args, **kwargs)
        return lhs <= rhs
    

class NetWorkGreaterEqual(NetWork):
                    
    def __call__(self, *args, **kwargs):
        lhs, rhs = self.forward(*args, **kwargs)
        return lhs >= rhs


class NetWorkEqual(NetWork):
                    
    def __call__(self, *args, **kwargs):
        lhs, rhs = self.forward(*args, **kwargs)
        import torch
        return torch.eq(lhs, rhs)


class NetWorkUnequal(NetWork):
                    
    def __call__(self, *args, **kwargs):
        lhs, rhs = self.forward(*args, **kwargs)
        import torch
        return torch.ne(lhs, rhs)
