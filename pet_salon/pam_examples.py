r'''
# Examples of Piecewise Affine Maps
'''
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

from sage.matrix.special import identity_matrix
from sage.modules.free_module import VectorSpace
from sage.rings.integer_ring import ZZ

from . import rectangle, PolytopeUnions, Partitions, AffineHomeomorphisms, SurjectiveImmersions
from .affine import PiecewiseAffineMaps

def integer_multiplication(dimension, field, k):
    r'''A representation of $v \mapsto k*v \pmod{\mathbb Z^d}$ as a piecewise affine map.

    The domain will be the cube $[0, 1]^d$ with $d$ the `dimension`. The map will be defined over the provided field. The parameter $k$ should be an integer that is at least $1$.

    EXAMPLES::

    Multiplication by 3 in two dimensions:

        sage: from pet_salon.pam_examples import integer_multiplication
        sage: f = integer_multiplication(2, QQ, 3)
        sage: f
        Multiplication by 3 in the 2-torus defined over Rational Field
        sage: f.partition().codomain()
        9 small 2-cubes
        sage: TestSuite(f).run()
        sage: domain = f.domain()
        sage: pt = domain.point((3/4, 2/3))
        sage: pt
        Point(0, (3/4, 2/3))
        sage: f(pt)
        Point(0, (1/4, 0))
        sage: f.is_surjective()
        True
        sage: f.is_injective()
        False
    '''
    from itertools import product

    assert k in ZZ and k>=1
    U = PolytopeUnions(dimension, field)
    cube = U({0: rectangle(field, *(dimension * [0, 1]))}, name = f'{dimension}-cube')
    P = Partitions(cube)
    G = U.affine_group()
    mult_by_k = k*identity_matrix(field, dimension)
    small_cube = rectangle(field, *(dimension * [0, 1/k]))
    small_cubes = {}
    affine_maps = {}
    label = 1
    V = VectorSpace(field, dimension)
    for coords in reversed(list(product(* dimension * [[i for i in range(k)],]))):
        v = V(coords)
        small_cubes[label] = small_cube + 1/k*v
        affine_maps[label] = G(mult_by_k, -v)
        label += 1
    small_cube_union = U(small_cubes, name = f'{len(small_cubes)} small {dimension}-cubes')
    p = P(small_cube_union)
    A = AffineHomeomorphisms(dimension, field)
    f = A(small_cube_union, affine_maps, codomain_is_nonoverlapping=False)
    multiple_copies_of_cube = f.codomain()
    I = SurjectiveImmersions(cube)
    d = {label:0 for label in multiple_copies_of_cube.labels()}
    i = I(multiple_copies_of_cube, d)
    PAMs = PiecewiseAffineMaps(dimension, field)
    pet = PAMs(p, f, i)
    pet.rename(f'Multiplication by {k} in the {dimension}-torus defined over {field}')
    return pet

