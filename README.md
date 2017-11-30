# Matroids-M2
A [matroid](https://en.wikipedia.org/wiki/Matroid) is a combinatorial structure abstracting the notion of (linear algebraic, graph-theoretic) independence. This package provides methods to perform computations with matroids in [Macaulay2](https://faculty.math.illinois.edu/Macaulay2/) (>= v1.5). Functionality includes:
- user-friendly creation of matroids from a matrix, graph, or ideal 
- converting between various equivalent representations such as bases/circuits/flats/hyperplanes 
- operations such as union, relaxation, deletion/contraction 
- testing of isomorphism and minors 
- computing Tutte polynomials and Chow rings

and more!

## Installation
To manually install the latest version: 

- Download the [source code](https://raw.githubusercontent.com/jchen419/Matroids-M2/master/Matroids.m2) (right-click, save link as -> "Matroids.m2")
- Open a Terminal window, and `cd` to the download location if necessary
- Start Macaulay2, and type `installPackage "Matroids"`
- Once installed, one can load the package (from any location) with `needsPackage "Matroids"`. Documentation can be viewed either in Terminal/Emacs with `help Matroids`, or in a browser with `viewHelp Matroids`
