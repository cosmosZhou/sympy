import axiom
import sys
# to run this script, please install:
# pip install mpmath==1.1.0       

if __name__ == '__main__':
    if len(sys.argv) == 1:
        axiom.prove.prove()
    else:        
        for package in sys.argv[1:]:
            package = package.replace('/', '.').replace('\\', '.')
            package = eval(package)
            ret = package.prove(package.__file__)
            if ret is False:
                print(package, 'is unproven')
            elif ret is None:
                print(package, 'is erroneous')

