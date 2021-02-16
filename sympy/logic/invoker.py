class Invoker:

    def __new__(cls, expr):
        this = object.__new__(cls)
        this._objs = []
        this._args = []
        this.index = []
        this._context = []
        this.append(expr)
        this.callable = None      
        return this
    
    @property
    def target(self):
        return self._objs[-1]
    
    @property
    def parent(self):
        return self._objs[-2]
    
    @property
    def source(self):
        return self._objs[0]
    
    def determine_assumptions(self, obj):
        if obj.is_Boolean:
            equivalent = obj.equivalent
            if equivalent is not None:
                if not isinstance(equivalent, (list, tuple)):
                    # in case of result of simplify                    
                    if equivalent is not self.target:
                        clue = equivalent.clue
                        if clue is not None:                        
                            return clue                    
            elif obj.given is not None:                
                parent = self.parent
                if parent.is_Sufficient and self.index[-1] == 0 or parent.is_Necessary and self.index[-1] == 1:
                    # in case of using imply
                    return 'imply'
                    
                assert not parent.is_Equivalent and not parent.is_ExprCondPair, "boolean conditions within ExprCondPair and Equivalent are not applicable for application in proof!" 
                    
                return 'given'
            elif obj.imply is not None:
                parent = self.parent
                assert not parent.is_Equivalent and not parent.is_ExprCondPair, "boolean conditions within ExprCondPair and Equivalent are not applicable for application in proof!"                
                return 'imply'
        return 'equivalent'
        
    def result(self, obj, simplify=True):
        kwargs = {self.determine_assumptions(obj) : self.source}

        for i in range(-1, -len(self.index) - 1, -1):
            this = self._objs[i - 1]
            args = [*this.args]
            args[self.index[i]] = obj
            
            if this.is_Interval:
                args += [this.left_open, this.right_open, this.is_integer]

            if i == -len(self.index):
                obj = this.func(*args, **kwargs)
            else:
                obj = this.func(*args)

            if simplify:
                obj = obj.simplify()
            
        if obj.equivalent == self.source and obj == self.source:
            return self.source
        return obj

    @property
    def this(self):
        return self.callable.__self__
        
    # simplify = True by default, use simplify = False in invoke, use simplify = None in simplification process after invoking!
    def __call__(self, *args, **kwargs):
        if self.callable is None:
            return self.enter(*args, **kwargs)
        
        this = self.this
        
        funcname = self.callable.__name__
        if funcname == 'subs':
            if not this.is_ConditionalBoolean:
                assert all(arg.is_Equal for arg in args)
                assert all(arg.plausible is None for arg in args)
        
        if this.is_ForAll:            
            if self.callable.__func__ is this.func.simplify:
                if self.parent.is_Exists:
                    kwargs['local'] = True
        
        obj = self.invoke(*args, **kwargs)
        
        return self.result(obj, simplify=kwargs.get('simplify', True) is not None)

    def invoke(self, *args, **kwargs):
        if self._context:
            this = self.this
            reps = []
            from sympy import Interval
            outer_context = {}
            for _, limits in self._context:
                for x, *ab in limits:
                    if len(ab) == 1:
                        domain, *_ = ab
                        if domain.is_Boolean:
                            domain = x.domain_conditioned(domain)                                                    
                    else:
                        domain = Interval(*ab, right_open=x.is_integer, integer=x.is_integer)
                        
                    if x in outer_context:
                        x, _domain = outer_context[x]
                        keys = domain.free_symbols & outer_context.keys()
                        if keys:
                            for key in keys:
                                domain = domain._subs(key, outer_context[key][0])
                        domain &= _domain
                            
                    _x = x.copy(domain=domain)
                    this = this._subs(x, _x).simplify()
                    reps.append((x, _x))
                    outer_context[x] = (_x, domain)
            
            obj = getattr(this, self.callable.__name__)(*args, **kwargs)  # .simplify()
            if obj.is_BooleanAtom:
                if obj.is_BooleanTrue:
                    parent = self.parent
                    if parent.is_ExprCondPair:
                        if self.target is parent.cond:
                            return self.target
                return obj                
                    
            
            reps.reverse()
            for x, _x in reps:
                _obj = obj._subs(_x, x)
                if obj.is_boolean:
                    if _obj.equivalent is not None:
                        if _obj.equivalent is not obj:
                            _obj.equivalent = None
                            if _obj is not obj:
                                _obj.equivalent = obj 
                    else:
                        if _obj.is_BooleanAtom:
                            _obj = _obj.copy(equivalent=obj)
                        else:
                            _obj.equivalent = obj
                obj = _obj                    
        else:                    
            obj = self.callable(*args, **kwargs)
        return obj
        
    def append(self, obj):
        self._objs.append(obj)

    method2index = {'rhs': 1,
                    'lhs': 0,
                    'function': 0,
                    'arg': 0,
                    'cond': 1,
                    'expr': 0,
                    'base': 0}

    def __getattr__(self, method):                
        target = self.target
        if method == 'T':
            if len(target.shape) > 1:
                return self
            
        obj = getattr(target, method)
        if callable(obj):
            self.callable = obj
            return self

        if isinstance(obj, tuple):
            self.append(obj)
            return self
        
        index = self.method2index.get(method)
        if index is None:
            return self.result(obj)
            
        self.index.append(index)
        self.append(obj)

        return self

    def __neg__(self):
        if self.target.is_Relational:
            self.callable = self.target.__neg__
            return self.__call__()

    def __sub__(self, rhs):
        if self.target.is_Relational:
            self.callable = self.target.__sub__
            return self.__call__(rhs)
        
    def __add__(self, rhs):
        if self.target.is_Relational:
            self.callable = self.target.__add__
            return self.__call__(rhs)
        
    def __truediv__(self, rhs):
        if self.target.is_Equality:
            self.callable = self.target.__truediv__
            return self.__call__(rhs)

    def __mul__(self, rhs):
        if self.target.is_Equality:
            self.callable = self.target.__mul__
            return self.__call__(rhs)

    def __mod__(self, rhs):
        if self.target.is_Equality:
            self.callable = self.target.__mod__
            return self.__call__(rhs)
        
    def __matmul__(self, rhs):
        if self.target.is_Equality:
            self.callable = self.target.__matmul__
            return self.__call__(rhs)

    def __str__(self):
        return str(self.target)

    @property
    def latex(self):
        return self.value.latex

    def __getitem__(self, indices):
        target = self.target
        
        if isinstance(target, tuple):
            obj = target[indices]
            self.index.append(self.parent.args.index(obj))
            self._objs[-1] = obj
        elif target.is_Tuple:
            self.index.append(indices)
            self._objs.append(target[indices])
        elif target.is_DenseMatrix:
            if isinstance(indices, tuple):
                i, j = indices
                index = i * target.cols + j + 1
            else:
                index = indices + 1
            
            self.index.append(index)
            self._objs.append(target.args[index])
        else:
            self = self.result(target[indices]) 
                        
        return self

    def __iter__(self):
        return iter(self.obj)

    def enter(self, *args, **kwargs):
        target = self.target
        limits = ()
        
        if target.is_ExprWithLimits:
            limits = target.limits
        elif target.is_ExprCondPair:
            piecewise = self.parent
            cond = target.cond
            for e, c in piecewise.args:
                if e == target.expr:
                    break
                cond &= c.invert()
                
            if cond.is_And:
                limits = tuple((eq.wrt, eq) for eq in cond.args)
            else: 
                limits = ((cond.wrt, cond),)
        if args:
            limits += tuple((x, target.domain_defined(x)) for x in args)
        if kwargs:
            shape = kwargs.get('shape', None)
            if shape is not None:
                limits = tuple(limit for limit in limits if limit[0].shape == shape)
                          
        self._context.append((target, limits))
        return self

#     def __exit__(self, *_):
#         self._context.pop()
#         if self._context:
#             target, _ = self._context[-1]
#             while self.target != target:
#                 self._objs.pop()
#                 self.index.pop()
#         
#         return self
    
    def __or__(self, x):
        if self.assumptions is None:
            self.assumptions = []
        target = self.target
        domain = target.domain_defined(x)
        self.assumptions.append((x, domain))
        return self


class Identity(Invoker):

    def result(self, obj):
        from sympy.core.relational import Relational
        from sympy import Equality
        
        for i in range(-1, -len(self.index) - 1, -1):
            this = self._objs[i - 1]
            args = [*this.args]
            args[self.index[i]] = obj
            obj = this.func(*args).simplify()            

        return Relational.__new__(Equality, self.source, obj)            
        
    def __call__(self, *args, **kwargs):
        if self.callable is None:
            return self.enter(*args)
        
        if self.callable.__name__ == 'subs':
            this = self.this
            if this.is_AddWithLimits:
                if len(args) == 2:
                    (x, *_), *_ = this.limits
                    # domain might be different!
                    assert args[0].name == x.name
#             elif self.obj.__self__.is_ConditionalBoolean:
#                 ...
            else:
                from sympy import Equality
                assert all(isinstance(arg, Equality) for arg in args)                

        obj = self.invoke(*args, **kwargs)
        
        return self.result(obj)

