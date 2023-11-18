mkdir -p dist
rm -f dist/*.tar.gz && python setup.py sdist && twine upload -r nexus dist/*.tar.gz
