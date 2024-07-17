# Pet Salon
A [SageMath](https://www.sagemath.org/) package to experiment with Polytope Exchange Transformations (PETs). Currently a work in progress.

## To install

First you need to install the prerequisites. We use [frozendict](https://github.com/Marco-Sulla/python-frozendict). To install run:
```
sage -pip install frozendict
```

Run from the directory containing this `README.md` file run the command:
```
sage -pip install .
```

To reinstall use:
```
sage -pip install --upgrade --force-reinstall .
```

## To test

From the current directory run the command:
```
sage -t pet_salon
```
To test an individual file run something like:
```
sage -t pet_salon/polyhedra.py
```
