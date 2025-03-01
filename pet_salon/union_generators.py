# ********************************************************************
#  This file is part of pet_salon.
#
#        Copyright (C) 2024 W. Patrick Hooper
#
#  pet_salon is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 2 of the License, or
#  (at your option) any later version.
#
#  pet_salon is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with pet_salon. If not, see <https://www.gnu.org/licenses/>.
# ********************************************************************

from collections.abc import Mapping

from sage.geometry.polyhedron.constructor import Polyhedron
from sage.rings.infinity import infinity
from sage.rings.integer_ring import ZZ
from sage.rings.rational_field import QQ

from pet_salon import PolytopeUnions

class _ZZ2mapping(Mapping):
    r'''The mapping sending ``v`` in $\mathbb Z^2$ to the square with lower-left hand corner ``v``.'''
    def __init__(self, unions):
        self._ZZ2 = ZZ.cartesian_product(ZZ)
        self._U = unions
    def __getitem__(self, key):
        if key in self._ZZ2:
            V = self._U.vector_space()
            v = V([*key]) # Convert to vector (neccessary for elements of ZZ2)
            return self._U.polyhedra()(Polyhedron(vertices=[v, v+V((1,0)), v+V((0,1)), v+V((1,1))]))
        else:
            raise KeyError
    def __iter__(self):
        return self._ZZ2.__iter__()
    def __len__(self):
        return infinity
    def __eq__(self, other):
        return isinstance(other, _ZZ2mapping)
    def __hash__(self):
        return hash('_ZZ2mapping')

def square_tiling(field):
    r'''
    Construct the square tiling in the plane as a PolytopeUnion.

    EXAMPLES::

        sage: from pet_salon.union_generators import square_tiling
        sage: union = square_tiling(QQ)
        sage: union
        Disjoint union of ∞ly many nonoverlapping polyhedra in QQ^2
        sage: TestSuite(union).run()
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
