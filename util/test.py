from util.search import read_all_py, axiom_directory
from run import project_directory

from util.cpp import instance as lib, vector
from ctypes import c_char_p, c_void_p
from _ctypes import Structure
from sympy.utilities.misc import Text
import re


class CodeBlock(Structure):
    _fields_ = [("ptr", c_void_p)]
    
    def __del__(self):
        lib.delete_CodeBlock(self)

    
def test():
    for py in read_all_py(project_directory()):
        print(py)
        with open(py, 'r') as file:
            text = file.read()
            print(text)
            break

def sparsemax(z):
    import numpy as np
    z_sorted = sorted(z, reverse=True)
    k = np.arange(len(z))
    k_array = 1 + k * z_sorted
    z_cumsum = np.cumsum(z_sorted) - z_sorted
    k_selected = k_array > z_cumsum
    k_max = np.where(k_selected)[0].max()
    threshold = (z_cumsum[k_max] - 1) / (k_max + 1)
    return np.maximum(z - threshold, 0)

def delete_duplicate():
    
    for py in read_all_py(axiom_directory()):
        
        [*lines] = Text(py)
        
        timestamp = {}
        for i, line in enumerate(lines):
            if m := re.match(r' *# *(created|updated) on (\d\d\d\d-\d\d-\d\d)', line):
                timestamp[m[1]] = (i, m[2])
        
        if len(timestamp) == 2:
            if timestamp['created'][1] == timestamp['updated'][1]:
                print('processing', py)
                print(timestamp)
                print('line to be deleted:', timestamp['updated'][0])
                print()
                
                index = timestamp['updated'][0]
                
                del lines[index]
                Text(py).writelines(lines)


if __name__ == '__main__':
    z = [0.5, 0.3, 0.1, 0.1, 0, 0.9] * 10
    
    z = sparsemax(z)
    _z = sparsemax(z, False)
    print(sum(z), sum(_z))
    print(z == _z)