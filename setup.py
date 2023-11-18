from setuptools import setup

if __name__ == "__main__":
    setup()

# usage of twine:
# pip install twine
# pip uninstall -y sympy.keras && python setup.py install
# del dist\*.tar.gz && python setup.py sdist && twine upload dist/*.tar.gz 
# pip uninstall -y sympy.keras && pip install --upgrade --no-cache-dir sympy.keras 
# pip install --upgrade --retries=50 sympy.keras -i https://pypi.Python.org/simple/