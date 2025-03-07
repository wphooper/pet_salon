r'''
Examples of Piecewise Affine Maps
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
from sage.matrix.constructor import matrix
from sage.misc.prandom import choice
from sage.modules.free_module import VectorSpace
from sage.rings.integer_ring import ZZ

from . import rectangle, PolytopeUnions, Partitions, AffineHomeomorphisms, SurjectiveImmersions, SurjectiveEmbeddings
from .affine import PiecewiseAffineMaps
from pet_salon.polyhedra import Polyhedron

def integer_multiplication(dimension, field, k):
    r'''A representation of :math:`v \mapsto k*v \pmod{\mathbb Z^d}` as a piecewise affine map.

    The domain will be the cube :math:`[0, 1]^d` with :math:`d` the ``dimension``\. The map will be defined over the provided field. The parameter :math:`k` should be an integer that is at least :math:`1`.

    EXAMPLES

    Multiplication by 3 in two dimensions::

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
    p = P.inverse(small_cube_union)
    A = AffineHomeomorphisms(dimension, field)
    f = A(small_cube_union, affine_maps, codomain_is_nonoverlapping=False)
    multiple_copies_of_cube = f.codomain()
    I = SurjectiveImmersions(cube)
    d = {label:0 for label in multiple_copies_of_cube.labels()}
    i = I(multiple_copies_of_cube, d)
    PAMs = PiecewiseAffineMaps(dimension, field)
    pet = PAMs(i, f, p)
    pet.rename(f'Multiplication by {k} in the {dimension}-torus defined over {field}')
    return pet

class CombinatorialConvexPolygonTriangulation:
    """
    A class to represent a combinatorial convex polygon triangulation.

    Attributes
    ----------
    _n : int
        The number of vertices of the polygon being triangulated.
    _triangles : set
        A set of frozensets, each containing three indices representing a triangle.
    _edges : set
        A set of frozensets, each containing two indices representing an edge.

    Methods
    -------
    __init__(n, triangles=None, edges=None):
        Initializes the triangulation with n vertices, and optionally with given triangles and edges.
    n():
        Returns the number of vertices of the polygon being triangulated.
    triangles():
        Returns the collection of triples of indices of vertices forming the triangles.
    edges():
        Returns the collection of pairs of indices of vertices forming the edges.
    flip(edge=None):
        Flips the given edge (or a random edge if none is provided) in the triangulation.
    surjective_embedding(vertices):
        Returns the surjective embedding associated with this triangulation of a polygon with the provided vertices.
    partition(vertices):
        Returns the partition associated with this triangulation of a polygon with the provided vertices.
    image(vertex_action):
        Returns the image of this triangulation under the provided vertex action.
    """
    def __init__(self, n, triangles = None, edges = None):
        assert n >= 3
        self._n = n
        if triangles == None:
            self._triangles = set([frozenset((0,i, i+1)) for i in range(1,n-1)])
            self._edges = set(frozenset((0,i)) for i in range(2, n-1))
        else:
            self._triangles = triangles
            if edges == None:
                edges = set()
                for i in range(0, len(triangles)):
                    tri0 = triangles[i]
                    for j in range(i+1, len(triangles)):
                        tri1 = triangles[j]
                        e = tri0.intersection(tri1)
                        if len(e)==2:
                            edges.add(e)
            self._edges = edges

    def n(self):
        r'''
        Return the number of vertices of the polygon being triangulated.
        '''
        return self._n

    def triangles(self):
        r'''
        Return the collection of triples of indices of vertices forming the triangles.
        '''
        return self._triangles

    def edges(self):
        r'''
        Return the collection of pairs of indices of vertices forming the edges.
        '''
        return self._edges

    def flip(self, edge=None):
        r'''
        Return the collection of pairs of indices of vertices forming the edges.
        '''
        if edge:
            e = frozenset(e)
            assert e in self.edges(), 'Attempted to flip in something that is not in the edges set.'
        else:
            e = choice(tuple(self.edges()))
        tris = []
        for t in self._triangles:
            if e.issubset(t):
                tris.append(t)
                if len(tris)==2:
                    break
        v0, = tris[0].difference(e)
        v1, = tris[1].difference(e)
        w0,w1 = e
        for t in tris:
            self._triangles.remove(t)
        self._triangles.add(frozenset((w0, v0, v1)))
        self._triangles.add(frozenset((w1, v0, v1)))
        self._edges.remove(e)
        self._edges.add(frozenset((v0,v1)))

    def surjective_embedding(self, vertices):
        r'''
        Return the surjective embedding associated to this triangulation of a polygon with the provided `vertices`, a list in cyclic order.
        '''
        P = PolytopeUnions(2, vertices[0].parent().base_ring())
        codomain = P(Polyhedron(vertices[0].parent().base_ring(), 2, vertices=vertices))
        SE = SurjectiveEmbeddings(codomain)
        return SE(P({ i : Polyhedron(vertices[0].parent().base_ring(), 2, vertices={vertices[a], vertices[b], vertices[c]}) for i, (a,b,c) in enumerate(self.triangles())}))

    def partition(self, vertices):
        r'''
        Return the partition associated to this triangulation of a polygon with the provided `vertices`, a list in cyclic order.
        '''
        return ~self.surjective_embedding(vertices)

    def image(self, vertex_action):
        r'''
        Return the image of this triangulation under the provided vertex_action.

        An example of a vertex action is `lambda i: (i+1)%n` where n is the number of vertices. This should be an element of the dihedral group.
        '''
        new_triangles = set()
        for a,b,c in self._triangles:
            new_triangles.add(frozenset((vertex_action(a), vertex_action(b), vertex_action(c))))
        new_edges = set()
        for a,b in self._edges:
            new_edges.add(frozenset((vertex_action(a), vertex_action(b))))
        return CombinatorialConvexPolygonTriangulation(self.n(), new_triangles, new_edges)

def polygon_triangulation_mapping(field, vertices, triangles, vertex_action = lambda n: n+1):
    r'''
    Return a Piecewise Affine Mapping of a convex n-gon that acts affinely on each triangle in a triangulation.

    Parameters determine the convex n-gon, a triangulation of it, and a (dihedral) action on vertices.

    :param field: A field containing the vertices
    :param vertices: A list of vertices. The length of the list is the n in n-gon.
    :param triangles: A list of triples of indices of vertices forming a triangulation of a convex n-gon.
    :param vertex_action: This determines the action on vertices, you can skip modding out by n, so examples are `lambda i: i+k` for a combinatorial rotation and `lambda i: k-i` for a reflection.
    '''
    PU = PolytopeUnions(2, field)
    V = PU.vector_space()
    vertices = [V(v) for v in vertices]
    n = len(vertices)
    assert len(triangles) == n-2, 'There should be two fewer triangles than vertices'
    quad = PU(Polyhedron(field, 2, vertices=vertices), name=f'The {n}-gon')
    domain = PU({i:PU.polyhedra()(Polyhedron(field, 2, vertices=[
            vertices[a],
            vertices[b],
            vertices[c],
        ])) for i,(a,b,c) in enumerate(triangles)})
    codomain = PU({i:PU.polyhedra()(Polyhedron(field, 2, vertices=[
            vertices[vertex_action(a)%n],
            vertices[vertex_action(b)%n],
            vertices[vertex_action(c)%n],
        ])) for i,(a,b,c) in enumerate(triangles)})
    G = PU.affine_group()
    def get_affine_transformation(G, v0, v1, v2, w0, w1, w2):
        r'''
        Construct the element of `G` sending $v_i \mapsto w_i$ for all $i$.
        '''
        I = G.one().A()
        step1 = G(I, -v0)
        MV = matrix([v1-v0, v2-v0]).transpose()
        MW = matrix([w1-w0, w2-w0]).transpose()
        step2 = G( MW * (~MV) )
        step3 = G(I, w0)
        return step3 * step2 *step1
    SE = SurjectiveEmbeddings(quad)
    p = ~SE(domain)
    AH = PU.affine_homeomorphisms()
    ah = AH(domain, { i: get_affine_transformation( G,
                                                    vertices[a],
                                                    vertices[b],
                                                    vertices[c],
                                                    vertices[vertex_action(a)%n],
                                                    vertices[vertex_action(b)%n],
                                                    vertices[vertex_action(c)%n],
                                                  ) for i,(a,b,c) in enumerate(triangles) } )
    assert ah.codomain() == codomain
    se = SE(codomain)
    #print('Warning: The polygon_triangulation_mapping function does not do much to test your input. Run `TestSuite(f).run()` to test and if it is incorrect, try to plot to see what is wrong.')
    return se * ah * p



def quadrilateral_map(field, vertices_or_vertex, vertex_action = lambda n: n+1, start_triangulation = 0):
    PU = PolytopeUnions(2, field)
    V = PU.vector_space()
    try:
        v = V(vertices_or_vertex)
        vertices = [
            V([0, 0]),
            V([1, 0]),
            v,
            V([0, 1]),
        ]
    except TypeError:
        vertices = [V(vertices_or_vertex[i]) for i in range(4)]
    quad = PU(Polyhedron(field, 2, vertices=vertices), name='Quadrilateral')
    tris = []
    for i in range(4):
        tris.append(PU.polyhedra()(Polyhedron(field, 2, vertices=[
            vertices[(i+1)%4],
            vertices[(i+2)%4],
            vertices[(i+3)%4],
        ])))
    # tris[i] is the triangle formed by removing vertex i
    domain = PU({ 1:tris[start_triangulation],
                  2: tris[(start_triangulation+2)%4]})
    codomain = PU({ 1: tris[vertex_action(start_triangulation)%4],
                    2: tris[vertex_action((start_triangulation+2)%4)%4]})
    G = PU.affine_group()
    def get_affine_transformation(G, v0, v1, v2, w0, w1, w2):
        r'''
        Construct the element of `G` sending $v_i \mapsto w_i$ for all $i$.
        '''
        I = G.one().A()
        step1 = G(I, -v0)
        MV = matrix([v1-v0, v2-v0]).transpose()
        MW = matrix([w1-w0, w2-w0]).transpose()
        step2 = G( MW * (~MV) )
        step3 = G(I, w0)
        return step3 * step2 *step1
    SE = SurjectiveEmbeddings(quad)
    p = ~SE(domain)
    AH = PU.affine_homeomorphisms()
    ah = AH(domain, { 1: get_affine_transformation(G, vertices[(start_triangulation+1)%4],
                                                      vertices[(start_triangulation+2)%4],
                                                      vertices[(start_triangulation+3)%4],
                                                      vertices[vertex_action((start_triangulation+1)%4)%4],
                                                      vertices[vertex_action((start_triangulation+2)%4)%4],
                                                      vertices[vertex_action((start_triangulation+3)%4)%4],
                                                      ),
                      2: get_affine_transformation(G, vertices[(start_triangulation+3)%4],
                                                      vertices[(start_triangulation)%4],
                                                      vertices[(start_triangulation+1)%4],
                                                      vertices[vertex_action((start_triangulation+3)%4)%4],
                                                      vertices[vertex_action((start_triangulation)%4)%4],
                                                      vertices[vertex_action((start_triangulation+1)%4)%4],
                                                      ),
                      })
    assert ah.codomain() == codomain
    se = SE(codomain)
    return se * ah * p

