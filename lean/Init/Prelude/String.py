from ..Structure import *
from ..Data.List import *
from .Char import *


class String(Structure):
    # Pack a `List Char` into a `String`. This function is overridden by the compiler and is O(n) in the length of the list.
    # Unpack `String` into a `List Char`. This function is overridden by the compiler and is O(n) in the length of the list.
    data = List[Char]

    def __new__(cls, data):
        self = super().__new__(cls)
        if isinstance(data, str):
            data = List[Char](*map(Char, data))
        self.args = data,
        return self

    def __getitem__(self, key):
        return self.data[key]

    def __len__(self):
        return len(self.data)
    
    def __iter__(self):
        return iter(self.data)

    def __str__(self):
        s = ''.join(chr(int(char.val)) for char in self)
        s = s.replace('"', '\\"')
        return f'"{s}"'


__all__ = 'String',