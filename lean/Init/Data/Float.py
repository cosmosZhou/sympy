from ..Structure import *


class Float(Structure):
    val = float

    def __lt__(self, rhs):
        return float(self) < float(rhs)

    def __gt__(self, rhs):
        return float(self) > float(rhs)

    def __le__(self, rhs):
        return float(self) <= float(rhs)
    
    def __ge__(self, rhs):
        return float(self) >= float(rhs)

    def __add__(self, rhs):
        return Float(float(self) + float(rhs))

    def __sub__(self, rhs):
        return Float(float(self) - float(rhs))

    def __float__(self):
        return self.arg
