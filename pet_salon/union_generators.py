from collections.abc import Mapping

from sage.geometry.polyhedron.constructor import Polyhedron
from sage.misc.cachefunc import cached_function
from sage.rings.infinity import infinity
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ
from sage.structure.unique_representation import UniqueRepresentation
from sage.structure.unique_representation import CachedRepresentation

from pet_salon import PolytopeUnions

class _ZZ2mapping(Mapping):
    def __init__(self, unions):
        self._ZZ2 = ZZ.cartesian_product(ZZ)
        self._U = unions
    def __getitem__(self, key):
        if key in self._ZZ2:
            V = self._U.vector_space()
            v = V(key)
            return self._U.polyhedra()(Polyhedron(vertices=[v, v+V((1,0)), v+V((0,1)), v+V((1,1))]))
        else:
            raise KeyError
    def __iter__(self):
        return self._ZZ2.__iter__()
    def __len__(self):
        return infinity


@cached_function
def square_tiling(field):
    r'''
    Construct the square tiling in the plane.

    EXAMPLES::

        sage: from pet_salon.union_generators import square_tiling
        sage: union = square_tiling(QQ)
        sage: union
        Disjoint union of infinitely many polyhedra in QQ^2
        sage: TestSuite(union).run(skip='_test_pickling')
        sage: union.polytope((2,1)).vertices()
        (A vertex at (2, 1),
         A vertex at (2, 2),
         A vertex at (3, 1),
         A vertex at (3, 2))
    '''
    U = PolytopeUnions(2, QQ, finite=False)
    mapping = _ZZ2mapping(U)
    union = U(mapping)
    return union
