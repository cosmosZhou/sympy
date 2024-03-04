"""Base class for all the objects in SymPy"""


def sympify(arg):
    if isinstance(arg, int):
        from sympy import Integer
        return Integer(arg)
    
    if isinstance(arg, float):
        from sympy import Rational
        arg10 = arg * 10
        if arg10 == 5:
            return Rational(1, 2)
        
        if arg10 == -5:
            return Rational(-1, 2)
        
        if arg10 == 2:
            return Rational(1, 5)
        
        if arg10 == -2:
            return Rational(-1, 5)
        
        from sympy import Float
        return Float(arg)
    
    if arg.is_IndexedOperator:
        return arg.basic
    return arg


class Basic:
    """
    Base Matcher class for all SymPy Matcher objects.
    """
    __slots__ = ('_args', '_assumptions', 'func', 'kwargs')

    # To be overridden with True in the appropriate subclasses
    is_number = False
    is_symbol = False
    is_bool = False
    is_set = False
    
    is_Basic = True
    is_Number = False
    is_Rational = False
    is_Integer = False
    is_EmptySet = False
    is_UniversalSet = False
    is_ImaginaryUnit = False
    is_ConditionSet = False
    is_Matrix = False
    is_Infinity = False
    is_NegativeInfinity = False
    is_One = False
    is_Integral = False
    is_Inference = False
    
    # Wanted is used in expression: Product + {Sum[Sum]}
    is_Wanted = False
    is_IndexedOperator = False

    def __new__(cls, *args, **kwargs):
        obj = object.__new__(Basic)
        obj.func = cls
        obj._args = args  # all items in args must be Basic objects
        
        #this will be used by the expression: BlockMatrix[1][Identity @ Expr]
        obj.kwargs = kwargs
        return obj

    @property
    def is_Add(self):
        return self.func.is_Add
    
    @property
    def is_Mul(self):
        return self.func.is_Mul
    
    @property
    def is_Pow(self):
        return self.func.is_Pow
    
    @property
    def is_MatMul(self):
        return self.func.is_MatMul
    
    @property
    def is_Boolean(self):
        return self.func.is_Boolean
    
    @property
    def is_Equal(self):
        return self.func.is_Equal
    
    @property
    def is_Unequal(self):
        return self.func.is_Unequal
    
    @property
    def is_Less(self):
        return self.func.is_Less
    
    @property
    def is_Greater(self):
        return self.func.is_Greater
    
    @property
    def is_LessEqual(self):
        return self.func.is_LessEqual
    
    @property
    def is_GreaterEqual(self):
        return self.func.is_GreaterEqual

    @property
    def is_Element(self):
        return self.func.is_Element
    
    @property
    def is_NotElement(self):
        return self.func.is_NotElement
    
    @property
    def is_Subset(self):
        return self.func.is_Subset
    
    @property
    def is_Supset(self):
        return self.func.is_Supset
    
    @property
    def is_NotSubset(self):
        return self.func.is_NotSubset
    
    @property
    def is_NotSupset(self):
        return self.func.is_NotSupset
    
    @property
    def is_Or(self):
        return self.func.is_Or

    @property
    def is_LatticeOp(self):
        return self.func.is_LatticeOp
    
    @property
    def is_And(self):
        return self.func.is_And
    
    @property
    def is_Infer(self):
        return self.func.is_Infer
    
    @property
    def is_Equivalent(self):
        return self.func.is_Equivalent
    
    @property
    def is_Assuming(self):
        return self.func.is_Assuming
    
    @property
    def is_ForAll(self):
        return self.func.is_ForAll

    @property
    def is_Exists(self):
        return self.func.is_Exists

    @property
    def is_BlockMatrix(self):
        return self.func.is_BlockMatrix
    
    @property
    def is_Transpose(self):
        return self.func.is_Transpose
    
    @property
    def is_abstract(self):
        return self.func.is_abstract
    
    @property
    def funcname(self):
        if self.kwargs:
            if len(self.kwargs) == 1:
                [value] = self.kwargs.values()
                return f"{self.func.__name__}[{value}]"
        return self.func.__name__
    
    def __str__(self):

        def repr(arg):
            if isinstance(arg, type):
                return arg.__name__
            return str(arg)
        
        if len(self.args) == 1:
            return '%s[%s]' % (self.funcname, repr(self.arg))
        
        if self.is_Add:
            return ' + '.join([repr(arg) for arg in self.args])
        
        if self.is_Mul:
            args = []
            for arg in self.args:
                s = repr(arg)
                if arg.is_Add:
                    s = "(%s)" % s
                args.append(s)
                
            return ' * '.join(args)
        
        if self.is_MatMul:
            args = []
            for arg in self.args:
                s = repr(arg)
                if arg.is_Add or arg.is_Mul:
                    s = "(%s)" % s
                args.append(s)
                
            return ' @ '.join(args)
        
        if self.is_Pow:

            def need_parenthesis(e):
                return e.is_Add or e.is_Mul or (e.is_Rational and not e.is_Integer)
            
            b, e = self.args
            if need_parenthesis(b):
                b = "(%s)" % repr(b)
            else:
                b = repr(b)
                
            if need_parenthesis(e):
                e = "(%s)" % repr(e)
            else: 
                e = repr(e)
                
            return '%s ** %s' % (b, e)
        
        if self.is_Or:
            args = []
            for arg in self.args:
                s = repr(arg)
                if arg.is_Infer or arg.is_Assuming or arg.is_Equivalent:
                    s = "(%s)" % s
                args.append(s)
                
            return ' | '.join(args)
        
        if self.is_And:
            args = []
            for arg in self.args:
                s = repr(arg)
                if arg.is_Or:
                    s = "(%s)" % s
                args.append(s)
                
            return ' & '.join(args)
        
        return "%s[%s]" % (self.funcname, ', '.join([repr(arg) for arg in self.args]))

    __repr__ = __str__

    @property
    def args(self):
        """Returns a tuple of arguments of 'self'.
        """
        return self._args
    
    @property
    def arg(self):
        return self._args[0]

    def typeof(self, cls):
        if isinstance(cls, type):
            return isinstance(self, cls)
        return self.typeof(cls.func)
    
    def of(self, cls, copy=False):
        args = self._extract(cls)
        if copy and isinstance(args, tuple):
            return [*args]
        return args
    
    def is_wanted(self):
        if self.is_Wanted:
            return True
        for arg in self.args:
            if isinstance(arg, type):
                continue
            if arg.is_wanted():
                return True
        return
    
    def find_path(self, cls, path):
        for i, arg in enumerate(self.args):
            if arg.typeof(cls):
                path.append(i)
                yield path
                path.pop()
                    
        for i, arg in enumerate(self.args):
            path.append(i)
            yield from arg.find_path(cls, path)                
            path.pop()

    def fetch_from_path(self, *path, struct=None):
        if struct is None:
            for index in path:
                self = self.args[index]        
            
            return self
            
        parent = []
        for index in path:
            parent.append(self)
            self = self.args[index]
        
        s = struct
        root_index = 0
        while True:
            if isinstance(s, type) or s.is_Wanted: 
                break
            
            assert isinstance(s, Basic)
            root_index -= 1
            
            for i in range(-1, -len(s.args) - 1, -1): 
                arg = s.args[i]
                if isinstance(arg, type):
                    continue
                if arg.is_wanted():
                    break
            else:
                raise Exception('not wanted??')
                
            s = s.args[i]
        
        if root_index == 0:
            if not self.instanceof(struct):
                raise
        else:
            root = parent[root_index]
            if not root.isinstance(struct, *path[root_index:]):
                raise
        
        return self
    
    def isinstance(self, cls, index, *path):
        assert isinstance(cls, Basic)
        
        if not isinstance(self, cls.func):
            return False
        
        for wantedIndex, s in enumerate(cls.args):
            if s.is_Wanted or isinstance(s, Basic) and s.is_wanted(): 
                if not self.args[index].instanceof(s):
                    return False
                break
        else:
            raise Exception('wanted not detected!')
        
        j = index - 1
        # scan backward, starting from wantedIndex - 1
        for i in range(wantedIndex - 1, -1, -1):
            struct = cls.args[i]
            if j < 0:
                break

            if isinstance(struct, type):
                if not isinstance(self.args[j], struct):
                    break
            elif struct.is_Number:
                if self.args[j] == struct:
                    ...
                elif self.args[j + 1] != struct:
                    break
                else:
                    continue
            else:
                if not self.args[j].isinstance(struct, *path):
                    break
            
            j -= 1
            
        else:
            j = index + 1
            # scan forward, starting from wantedIndex + 1
            for i in range(wantedIndex + 1, len(cls.args)):
                if j >= len(self.args):
                    break

                struct = cls.args[i]
                if isinstance(struct, type):
                    if not isinstance(self.args[j], struct):
                        break
                elif struct.is_Number:
                    if self.args[j] == struct:
                        ...
                    elif self.args[j + 1] != struct:
                        break
                    else:
                        continue
                else:
                    if not self.args[j].isinstance(struct, *path):
                        break
                    
                j += 1
                
            else:
                return True
                
        return False
        
    def instanceof(self, cls):
        if isinstance(cls, type):
            return isinstance(self, cls)
        
        if cls.is_Wanted: 
            if isinstance(cls.func, type):
                return isinstance(self, cls.func)
            
            cls = cls.func
                
        if not isinstance(self, cls.func):
            return False
        j = 0
        i = 0
        while j < len(self.args):
            struct = cls.args[i]
            if self.args[j].instanceof(struct):
                i += 1
                if i == len(cls.args):
                    break
            j += 1
        else:
            return i == len(cls.args)
            
        return True
    
    def _extract(self, cls):
        if isinstance(cls, type):
            if isinstance(self, cls):
                args = self.args
                if len(args) == 1:
                    return args[0]
                return args
            else:
                return
        
        if not isinstance(self, cls.func):
            return
        j = 0
        i = 0
        
        args = []
        while j < len(self.args):
            struct = cls._args[i]
            this = self.args[j]
            arg = this.of(struct)
            if arg is not None:
                if arg == ():
                    from sympy import Symbol
                    if this.is_Symbol and (struct is Symbol or not struct.is_Symbol) or \
                    this.is_Number and not struct.is_Number:
                        args.append(this)
                else:
                    is_abstract = struct.is_abstract if isinstance(struct, type) else False
                    args.append(this if is_abstract else arg)
                    
                i += 1
                if i == len(cls._args):
                    args.extend(self.args[j + 1:])
                    break
            else:
                args.append(this)
                
            j += 1
        else:
            if i == len(cls._args):
                return ()
            else:
                return
            
        args = tuple(args)
        while isinstance(args, tuple):
            if len(args) == 1:
                args = args[0]
            elif not args:
                return ()
            else:
                break
            
        return args
    
    @staticmethod
    def make_query(*query):
        if len(query) > 1 or isinstance(query[0], type): 
            if isinstance(query[-1], type):
                struct = None
            else:
                q, struct = Basic.make_query(query[-1])
                query = [*query[:-1]] + q
        else:
            struct = query[0]
            
            if not struct.is_Basic: 
                struct = struct.basic
                
            if not struct.is_wanted():
                from sympy.core.core import Wanted
                struct = Wanted(struct)
                    
            query = []
            s = struct
            while True:
                if isinstance(s, type) or s.is_Wanted:
                    query.append(s)
                    break
                
                if not s.is_Basic:
                    assert s.is_IndexedOperator
                    s = s.basic
                
                query.append(s.func)
                
                for i in range(-1, -len(s.args) - 1, -1):
                    arg = s.args[i]
                    if isinstance(arg, type):
                        continue
                    if arg.is_wanted():
                        break
                else:
                    raise Exception('not wanted??')
                s = s.args[i]
            
        return query, struct
        
    def find(self, *query): 
        query, struct = Basic.make_query(*query)
            
        return self.yield_one([(q, []) for q in query],
                            foreach=Basic.find_path,
                            func=Basic.fetch_from_path,
                            fetch=self.fetch_from_path,
                            output=[],
                            struct=struct)
                    
    def finditer(self, *query):
        query, struct = Basic.make_query(*query)
        try:
            yield from self.yield_all([(q, []) for q in query],
                            foreach=Basic.find_path,
                            func=Basic.fetch_from_path,
                            fetch=self.fetch_from_path,
                            output=[],
                            struct=struct)
        except GeneratorExit:
            ...
        
    def yield_one(self,
                limits,
                foreach=None,
                                
                func=None,
                fetch=None,
                output=None,
                
                **kwargs): 
            
        limit, *limits = limits
        
        for _output in foreach(self, *limit):
            try: 
                if not limits: 
                    return fetch(*output, *_output, **kwargs)
                
                return func(self, *_output).yield_one(limits,
                                                    foreach=foreach,
                                                    func=func,
                                                    fetch=fetch,
                                                    output=output + _output,
                                                    **kwargs)
            except:
                continue
            
        raise
                    
    def yield_all(self,
                limits,
                foreach=None,
                                
                func=None,
                fetch=None,
                output=None,
                
                **kwargs): 
            
        limit, *limits = limits
        for _output in foreach(self, *limit):
            try: 
                if not limits: 
                    yield fetch(*output, *_output, **kwargs)
                else:
                    yield from func(self, *_output).yield_all(limits,
                                                    foreach=foreach,
                                                    func=func,
                                                    fetch=fetch,
                                                    output=output + _output,
                                                    **kwargs)
            except GeneratorExit as e:
                raise e
            except: 
                continue
        
    def __add__(self, other):
        from sympy import Add
        other = sympify(other)
        if other.is_Integer: 
            if self.is_Add:
                args = other, *self.args
            else:
                args = other, self
            
        elif self.is_Add:
            if other.is_Add:
                args = *other.args, *self.args
            else:
                args = *self.args, other
        else:
            args = self, other

        return Basic.__new__(Add, *args)

    def __radd__(self, lhs):
        from sympy import Add
        lhs = sympify(lhs)
        return Basic.__new__(Add, lhs, self)

    def __rsub__(self, lhs):
        lhs = sympify(lhs)
        self = -self
        return Basic.__add__(lhs, self)
    
    def __mul__(self, other):
        from sympy import Mul
        other = sympify(other)
        if other.is_Integer or other.is_Infinity or other.is_NegativeInfinity:
            if self.is_Mul:
                args = other, *self.args
            else:
                args = other, self
        else:
            if self.is_Mul:
                if other.is_Mul:
                    args = *self.args, *other.args
                else:
                    args = *self.args, other
            elif other.is_Mul:
                args = self, *other.args
            else:
                args = self, other 
        return Basic.__new__(Mul, *args)

    def __rmul__(self, lhs):
        from sympy import Mul
        lhs = sympify(lhs)
        if lhs.is_Mul:
            args = *lhs.args, self
        else:
            args = lhs, self
        return Basic.__new__(Mul, *args)

    def __matmul__(self, other):
        from sympy import MatMul
        other = sympify(other)
        if self.is_MatMul:
            args = *self.args, other 
        else:
            args = self, other
        return Basic.__new__(MatMul, *args)

    def __sub__(self, other):
        from sympy import Add
        other = sympify(other)
        other = -other
        
        if other.is_Integer: 
            if not self.is_Number:
                if self.is_Add:
                    args = other, *self.args
                else:
                    args = other, self
                
                return Basic.__new__(Add, *args)
            
        if self.is_Add:
            args = *self.args, other
        else:
            args = self, other
        return Basic.__new__(Add, *args)

    def __neg__(self):
        from sympy import Mul, S
        if self.is_Mul:
            if self.args[0].is_Number:
                args = -self.args[0], *self.args[1:]
            else:
                args = S.NegativeOne, *self.args
        else:
            args = (S.NegativeOne, self)
            
        return Basic.__new__(Mul, *args)
    
    def __invert__(self):
        from sympy.core.core import Wanted
        return Wanted(self)
    
    @property
    def unwanted(self):
        hit = False
        args = []
        for arg in self.args:
            unwanted = getattr(arg, 'unwanted', arg)
            hit |= unwanted is not arg
            args.append(unwanted)

        if hit:
            return Basic.__new__(self.func, *args)
        return self

    def __floordiv__(self, other):
        from sympy import Floor
        other = sympify(other)     
        return Basic.__new__(Floor, self / other)
    
    def __truediv__(self, other):
        from sympy import Mul, Pow, S
        other = sympify(other)
        if other.is_Integer:
            other = 1 / other
            if self.is_Mul:
                if self.args[0].is_Number:
                    args = other * self.args[0], *self.args[1:]
                else:
                    args = other, *self.args
            else:
                args = other, self
        else:
            other = Basic.__new__(Pow, other, S.NegativeOne)
            if self.is_Mul:
                args = *self.args, other
            else:
                args = self, other
        return Basic.__new__(Mul, *args)
    
    def __rtruediv__(self, lhs):
        from sympy import Mul, Pow, S
        lhs = sympify(lhs)
        
        pow = Basic.__new__(Pow, self, S.NegativeOne)
        if lhs == 1:
            return pow
        return Basic.__new__(Mul, lhs, pow)

    def __mod__(self, other):
        from sympy import Mod
        other = sympify(other)
        return Basic.__new__(Mod, self, other)
    
    def __pow__(self, other):
        from sympy import Pow
        other = sympify(other)
        return Basic.__new__(Pow, self, other)
    
    def __rpow__(self, lhs):
        from sympy import Pow
        lhs = sympify(lhs)
        return Basic.__new__(Pow, lhs, self)
    
    def __gt__(self, other):
        from sympy import Greater
        other = sympify(other)
        return Basic.__new__(Greater, self, other)

    def __ge__(self, other):
        from sympy import GreaterEqual
        other = sympify(other)
        return Basic.__new__(GreaterEqual, self, other)

    def __lt__(self, other):
        from sympy import Less
        other = sympify(other)
        return Basic.__new__(Less, self, other)

    def __le__(self, other):
        from sympy import LessEqual
        other = sympify(other)
        return Basic.__new__(LessEqual, self, other)

    def __and__(self, other):
        other = sympify(other)
        if self.is_Boolean:
            from sympy import And
            if self.is_And:
                return Basic.__new__(And, *self.args, other)
            
            obj = Basic.__new__(And, self, other)
        else:
            from sympy import Intersection
            obj = Basic.__new__(Intersection, self, other)
#         obj._argset = (self, other)
        return obj
    
    __rand__ = __and__

    def __or__(self, other):
        other = sympify(other)
        if self.is_Boolean:
            from sympy import Or
            if self.is_Or:
                return Basic.__new__(Or, *self.args, other)
            
            obj = Basic.__new__(Or, self, other)
        else:
            from sympy import Union
            obj = Basic.__new__(Union, self, other)
#         obj._argset = (self, other)
        return obj
    
    def of_LinearPattern(self):
        if self.is_Mul and len(self.args) == 2:
            num, basic = self.args
            from sympy import S
            if num == -1 or num.is_ImaginaryUnit:
                try:
                    return basic.is_abstract
                except AttributeError:
                    ...
            num, basic = basic, num
            if num == -1 or num.is_ImaginaryUnit:
                try:
                    return basic.is_abstract
                except AttributeError:
                    ...

    def of_subtraction_pattern(self):
        if self.is_Add and len(self.args) == 2:
            basic, mul = self.args
            if mul.is_Mul:
                if len(mul.args) == 2:
                    negativeOne, var = mul.args
                    if negativeOne == -1:
                        return var.is_abstract
        
    def of_two_terms(self):
        if self.is_Add and len(self.args) == 2:
            basic, mul = self.args
            try:
                return basic.is_abstract
            except AttributeError:
                ...

    def of_simple_poly(self):
        if self.is_Add and len(self.args) == 2:
            from sympy import Expr
            try:
                index = self.args.index(Expr)
                mul = self.args[1 - index]
                if mul.is_Mul:
                    if len(mul.args) == 2:
                        if Expr in mul.args:
                            return True
            except:
                ...

