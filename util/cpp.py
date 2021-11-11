from ctypes import *

import numpy as np
import os
from util.std import is_Linux, cstring

ctypes2numpy = {"?": np.bool,
          "c": np.char,
          "b": np.byte,
          "B": np.ubyte,
          "f": np.float32,
          "d": np.double,
          "g": np.longdouble,
          "h": np.short,
          "H": np.ushort,
          "i": np.int32,
          "I": np.uint32,
          "l": np.long,
          "q": np.longlong,
          "Q": np.ulonglong,
          }


class VectorBase:

    def __len__(self):
        end = cast(self._M_finish, c_void_p).value
        start = cast(self._M_start, c_void_p).value
        if start is None:
            assert end is None
            return 0   
        return (end - start) // sizeof(self.etype)
        
    def __iter__(self):
        for i in range(len(self)):
            yield reference(self.etype, self._M_start, i)
         
    def delete(self): 
        for el in self:
            if isinstance(el, reference):
                el.delete()
            else:
                del el
        instance.destruct(cast(self._M_start, c_void_p))
            
    def __str__(self):
        arr = []
        for e in self:
            arr.append(str(e))
        return "[%s]" % ', '.join(arr)
    
    __repr__ = __str__

    def tolist(self):
        arr = []
        for e in self:
            if hasattr(e, 'tolist'):
                e = e.tolist()
            elif isinstance(e, (String, string)):
                e = str(e)
            else:
                ...            
            arr.append(e)
        return arr

    def __getitem__(self, i):
        
        if isinstance(i, slice):
            start, stop = i.start, i.stop
            assert i.step is None, 'step is not supported yet'
            if start is None:
                start = 0
            if stop is None:
                stop = len(self)
                
            return [reference(self.etype, self._M_start, i) for i in range(start, stop)]
        
        if isinstance(i, int) and i < 0:
            i += len(self)
        return reference(self.etype, self._M_start, i)



class reference(VectorBase):

    def __new__(cls, vector, _M_start, index):
        if hasattr(vector, 'etype'):
            obj = object.__new__(cls)
            etype = vector.etype
            ptr = cast(cast(cast(_M_start, c_void_p).value + index * 24, c_void_p), POINTER(POINTER(etype)))
            obj._M_start = ptr[0]
            obj._M_finish = ptr[1]            
            obj.etype = etype
            return obj
        else:
            return _M_start[index]        

        
def vector(Element_Type):
    pointer = POINTER(Element_Type)
            
    class vector(Structure, VectorBase):
        _fields_ = [("_M_start", pointer), ("_M_finish", pointer), ("_M_end_of_storage", pointer)]
        
        etype = Element_Type
        
        def __init__(self, *args):
            if len(args) == 1: 
                [args] = args
            # allocate memory before the final allocation occurs!
            args = [Element_Type(x) for x in args]
                        
            self.resize(len(args))
            
            for i, x in enumerate(args):
                self[i] = x
                
        def __bool__(self):
            return len(self) != 0
        
        def __del__(self): 
            self.delete()
                
        def resize(self, size):
            length = size * sizeof(Element_Type)
            self._M_start = cast(instance.construct(length), pointer)
            self._M_finish = cast(cast(cast(self._M_start, c_void_p).value + length, c_void_p), pointer)
            
            self._M_end_of_storage = self._M_finish
            instance.stosb(self._M_start, 0, length)
    
        def capacity(self):
            return (cast(self._M_end_of_storage, c_void_p).value - cast(self._M_start, c_void_p).value) // sizeof(Element_Type)
    
        def __setitem__(self, i, value):
            if isinstance(i, int) and i < 0: 
                i += len(self)
            obj = self._M_start[i]
            del obj
            
            self._M_start[i] = value
            if hasattr(self.etype, 'etype'):
                etype = self.etype.etype
                nullptr = cast(cast(0, c_void_p), POINTER(etype))
                value._M_start = nullptr
                value._M_finish = nullptr
                value._M_end_of_storage = nullptr
    
        def __eq__(self, rhs):
            size = len(self)
            if size != len(rhs):
                return False
            for i in range(size):
                if self[i] != rhs[i]:
                    return False
            return True

        @classmethod
        def dtype(cls):
            if hasattr(Element_Type, '_type_'):
                return ctypes2numpy.get(Element_Type._type_)
            if hasattr(Element_Type, 'dtype'):
                return Element_Type.dtype()
        
        def numpy(self): 
            arr = []
            for e in self:
                if hasattr(e, 'numpy'):
                    e = e.numpy()
                arr.append(e)
            dtype = self.dtype()
            if dtype is not None:
                return np.array(arr, dtype=dtype)
            return np.array(arr)
        
        @classmethod
        def POINTER(cls):
            return POINTER(cls)
    
    return vector


def pair(First_Type, Second_Type):

    class pair(Structure):
        _fields_ = [("first", First_Type), ("second", Second_Type)]

        def __init__(self, first=None, second=None):
            if first is None:
                first = First_Type()
                
            if second is None:
                second = Second_Type()
                
            self.first = first
            self.second = second
                    
        def __str__(self):
            return "(%s, %s)" % (str(self.first), str(self.second))
        
        __repr__ = __str__
        
        def __eq__(self, rhs):
            return self.first == rhs.first and self.second == rhs.second

        def tolist(self):
            return [self.first, self.second]
    
        @classmethod
        def POINTER(cls):
            return POINTER(cls)
    
    return pair


VectorI = vector(c_int32)
MatrixI = vector(VectorI)
TensorI = vector(MatrixI)

VectorD = vector(c_double)
MatrixD = vector(VectorD)
TensorD = vector(MatrixD)
Array4D = vector(TensorD)

VectorF = vector(c_float)
MatrixF = vector(VectorF)
TensorF = vector(MatrixF)
Array4F = vector(TensorF)

VectorZ = vector(c_bool)
MatrixZ = vector(VectorZ)
TensorZ = vector(MatrixZ)
Array4Z = vector(TensorZ)


class Lagacy:

    slots = ('lib',)

    def __init__(self):
        workingDirectory = os.path.dirname(__file__) + '/../'
        lib = 'engine'
        if not os.path.exists(workingDirectory + lib):
            workingDirectory += '../'
            assert os.path.exists(workingDirectory + lib)
        
        if is_Linux():  # is Linux System
            self.lib = cdll.LoadLibrary(workingDirectory + f'{lib}/Linux/lib{lib}.so')                                
        else:  # is Windows System
            os.add_dll_directory(os.environ.get('MINGW_HOME') + '/bin')
            self.lib = cdll.LoadLibrary(workingDirectory + f'{lib}/Release/{lib}.dll')
        
        # self.initialize_working_directory[c_char_p] = None        
        # self.initialize_working_directory(cstring(workingDirectory))
    
        self.sizeof_string[()] = c_uint
        # self.construct[c_ulonglong] = c_void_p
        # self.destruct[c_void_p] = None
        # self.stosb[c_void_p, c_byte, c_ulonglong] = None

    def __getattr__(self, funcname):
        if funcname in self.__dict__:
            return self.__dict__[funcname]
        
        dll = self
        func = getattr(self.lib, funcname)

        class CFunction: 

            def __setitem__(self, argtypes, restype):
                if not isinstance(argtypes, (list, tuple)):
                    argtypes = [argtypes]
                if is_Linux():

                    def enumerate():
                        for t in argtypes:
                            if t.__class__.__name__ == 'PyCStructType':
                                yield POINTER(t)
                            else:
                                yield t
                                
                    argtypes = [*enumerate()]

                func.argtypes = argtypes
                func.restype = restype
                dll.__dict__[func.__name__] = func
        
        return CFunction()


instance = Lagacy()

if instance.sizeof_string() == 8:
    offset = 24
    
    class String(Structure):
        pointer = POINTER(c_ushort)
        
        _fields_ = [("_M_dataplus", pointer)]
    
        _CharT = c_ushort
        
        def __init__(self, text):
            self.resize(len(text))
            for i in range(len(text)):
                self[i] = text[i]
            
        def __str__(self):
            return ''.join(chr(self._M_dataplus[i]) for i in range(len(self)))
    
        def __getitem__(self, i):
            return self._M_dataplus[i]
    
        def __setitem__(self, i, value):
            self._M_dataplus[i] = c_ushort(ord(value))
    
        def resize(self, size):
            array = instance.construct(offset + (size + 1) * 2)
            _Rep = cast(array, POINTER(c_ulonglong))
            _Rep[0] = c_ulonglong(size)
            _Rep[1] = c_ulonglong(size)
            
            self._M_dataplus = cast(byref(array, offset), self.pointer)
            assert not self._M_dataplus[size]
    
        def __len__(self):
            return cast(self._M_dataplus, POINTER(c_ulonglong))[-3]
    
        def __eq__(self, rhs):
            return str(self) == str(rhs)
        
        def __del__(self):
            instance.destruct(cast(byref(self._M_dataplus, -offset), c_void_p))
    
    class string(Structure):
        pointer = POINTER(c_char)
        _fields_ = [("_M_dataplus", pointer)]
    
        _CharT = c_char
        
        def __init__(self, text):
            text = cstring(text)
            self.resize(len(text))
            for i in range(len(text)):
                self[i] = text[i]
    
        def __setitem__(self, i, value):
            self._M_dataplus[i] = c_char(value)
        
        def __str__(self):
            return self._M_dataplus.decode('utf8')
    
        def __getitem__(self, i):
            return self._M_dataplus[i]
    
        def __len__(self):
            return cast(self._M_dataplus, POINTER(c_ulonglong))[-3]
    
        def __eq__(self, rhs):
            return str(self) == str(rhs)
    
        def resize(self, size):
            array = instance.construct(offset + size + 1)

            _Rep = cast(array, POINTER(c_ulonglong))
            _Rep[0] = c_ulonglong(size)
            _Rep[1] = c_ulonglong(size)

            self._M_dataplus = cast(byref(array, offset), self.pointer)
            assert not ord(self._M_dataplus[size])
            
        def __del__(self):
            instance.destruct(cast(byref(self._M_dataplus, -offset), c_void_p))

else: 

    class String(Structure):
        pointer = POINTER(c_ushort)
        
        _fields_ = [("_M_dataplus", pointer), ("_M_string_length", c_uint), ("_M_local_buf", c_ushort * 8)]
    
        _CharT = c_ushort
        
        def __init__(self, text):
            self.resize(len(text))
            for i in range(len(text)):
                self[i] = text[i]
            
        def __str__(self):
            return ''.join(chr(self._M_dataplus[i]) for i in range(self._M_string_length))
    
        def __getitem__(self, i):
            return self._M_dataplus[i]
    
        def __setitem__(self, i, value):
            self._M_dataplus[i] = c_ushort(ord(value))
    
        def resize(self, size):
            array = instance.construct((size + 1) * 2)
    
            self._M_dataplus = cast(array, self.pointer)
            self._M_string_length = c_uint(size)
            assert not self._M_dataplus[size]
    
        def __len__(self):
            return self._M_string_length
    
        def __eq__(self, rhs):
            return str(self) == str(rhs)
    
        def __del__(self):
            instance.destruct(cast(self._M_dataplus, c_void_p))

    class string(Structure):
        pointer = POINTER(c_char)
        
        _fields_ = [("_M_dataplus", pointer), ("_M_string_length", c_uint), ("_M_local_buf", c_char * 16)]
    
        _CharT = c_char
        
        def __init__(self, text):
            text = cstring(text)
            self.resize(len(text))
            for i in range(len(text)):
                self[i] = text[i]
    
        def __setitem__(self, i, value):
            self._M_dataplus[i] = c_char(value)
        
        def __str__(self):
            return self._M_dataplus.decode('utf8')
    
        def __getitem__(self, i):
            return self._M_dataplus[i]
    
        def __len__(self):
            return self._M_string_length
    
        def __eq__(self, rhs):
            return str(self) == str(rhs)
    
        def resize(self, size):
            array = instance.construct(size + 1)
    
            self._M_dataplus = cast(array, self.pointer)
            self._M_string_length = c_uint(size)
            assert not ord(self._M_dataplus[size])

        def __del__(self):
            instance.destruct(cast(self._M_dataplus, c_void_p))

VectorS = vector(String)
MatrixS = vector(VectorS)

if __name__ == '__main__':

    def local():
        arr = MatrixI([[0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]])
        print(arr.tolist())
        print(arr.tolist())
        print(arr.tolist())
        
    local()

