# ********************************************************************
#  This file is part of pet-salon.
#
#        Copyright (C) 2024 W. Patrick Hooper
#
#  sage-flatsurf is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 2 of the License, or
#  (at your option) any later version.
#
#  sage-flatsurf is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with sage-flatsurf. If not, see <https://www.gnu.org/licenses/>.
# ********************************************************************
from collections.abc import Mapping
from frozendict import frozendict

from sage.categories.all import Sets
from sage.categories.category import Category
from sage.misc.abstract_method import abstract_method
from sage.misc.cachefunc import cached_method
from sage.misc.sage_unittest import TestSuite
from sage.rings.infinity import infinity
from sage.structure.element import Element
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation

from pet_salon.affine_gps.affine_group import AffineGroup

from .collection import identity_mapping, function_mapping, length
from .immersion import Immersions, Partitions, SurjectiveEmbeddings, PartitionsCategory, ImmersionsCategory
from .label import Relabeler
from .union import PolytopeUnions

class AffineHomeomorphismsCategory(Category):
    r'''The category of (label respecting) affine homeomorphisms between polytope unions.'''
    def __init__(self, *args, **options):
        Category.__init__(self, *args, **options)
        self.rename(f'Category of affine homeomorphisms between polytope unions')

    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.
        """
        return [Sets()]

    class SubcategoryMethods:
        pass

    class ParentMethods:

        @abstract_method
        def field(self):
            pass

        @abstract_method
        def dimension(self):
            pass

        @abstract_method
        def trivial_affine_homeomorphism(self, union):
            r'''Return the trivial affine homeomorphism of union into union.'''
            pass

        def affine_group(self):
            return AffineGroup(self.dimension(), self.field())

        def _an_element_(self):
            return self.trivial_affine_homeomorphism(
                PolytopeUnions(self.dimension(), self.field()).an_element()
            )

        @cached_method
        def piecewise_affine_maps(self):
            return PiecewiseAffineMaps(self.dimension(), self.field())

    class ElementMethods:

        @abstract_method
        def domain(self):
            pass

        @abstract_method
        def codomain(self):
            pass

        @abstract_method
        def affine_mapping(self):
            r'''
            Return a mapping sending labels to the corresponding element of the affine group
            '''
            pass

        def _test_parents(self, tester=None, limit=20):
            assert self.domain().parent().field() == self.parent().field(), \
                'The domain\'s field is incorrect.'
            assert self.codomain().parent().field() == self.parent().field(), \
                'The codomain\'s field is incorrect.'
            assert self.domain().parent().dimension() == self.parent().dimension(), \
                'The domain\'s dimension is incorrect.'
            assert self.codomain().parent().dimension() == self.parent().dimension(), \
                'The codomain\'s dimension is incorrect.'

            G = self.parent().affine_group()
            if self.domain().is_finite():
                for label in self.domain().labels():
                    assert self.affine_mapping()[label] in G, f'The image of label {label} is not in {G}'
            else:
                for label,_ in zip(self.domain().labels(), range(limit)):
                    assert self.affine_mapping()[label] in G, f'The image of label {label} is not in {G}'

        def __call__(self, x):
            r'''Return the image of x under the mapping.

            EXAMPLES::

                sage: from pet_salon import PolytopeUnions, rectangle
                sage: from pet_salon.affine import AffineHomeomorphisms
                sage: U = PolytopeUnions(2, QQ)
                sage: domain = U(rectangle(QQ, 0, 1, 0, 1))
                sage: domain.rename('Square')
                sage: Aff = U.affine_group()
                sage: A = U.affine_homeomorphisms()
                sage: A
                Collection of label-respecting affine homeomorphisms of disjoint unions of 2-dimensional polytopes defined over Rational Field
                sage: a = Aff([[1, 1],[0,1]], [1,1])
                sage: a
                      [1 1]     [1]
                x |-> [0 1] x + [1]
                sage: f = A(domain, {0: a}, codomain_is_nonoverlapping=True)
                sage: f
                Affine homeomorphism between disjoint unions of 1 polytopes
                sage: f.codomain().polytope(0).vertices()
                (A vertex at (1, 1),
                 A vertex at (2, 1),
                 A vertex at (2, 2),
                 A vertex at (3, 2))
                sage: image_point = f(domain.point((1/2,1/2)))
                sage: image_point
                Point(0, (2, 3/2))
                sage: TestSuite(image_point).run()
            '''
            if x in self.domain().point_set():
                return self.codomain().point(x.label(), self.affine_mapping()[x.label()](x.position()))

        def _test_domain_and_codomain(self, tester=None):
            r'''Check the domain and codomain for errors.

            EXAMPLES::

                sage: from pet_salon import PolytopeUnions
                sage: U = PolytopeUnions(2, QQ)
                sage: p0 = Polyhedron(vertices=[(0,0), (1,0), (0,1)])
                sage: p1 = Polyhedron(vertices=[(1,0), (1,1), (0,1)])
                sage: domain = U({0: p0, 1: p1})
                sage: domain
                Disjoint union of 2 nonoverlapping polyhedra in QQ^2
                sage: Aff = U.affine_group()
                sage: a0 = Aff([[1, 1], [0, 1]])
                sage: a0
                      [1 1]     [0]
                x |-> [0 1] x + [0]
                sage: a1 = Aff.one()
                sage: a1
                      [1 0]     [0]
                x |-> [0 1] x + [0]
                sage: A = U.affine_homeomorphisms()
                sage: A
                Collection of label-respecting affine homeomorphisms of disjoint unions of 2-dimensional polytopes defined over Rational Field
                sage: f = A(domain, {0: a0, 1: a1}, codomain_is_nonoverlapping=True)
                sage: f._test_domain_and_codomain()
                Traceback (most recent call last):
                ...
                AssertionError...
            '''
            try:
                TestSuite(self.domain()).run(catch=False, raise_on_failure=True)
            except Exception as e:
                raise AssertionError(f'The domain has an error: {e}')
            try:
                TestSuite(self.codomain()).run(catch=False, raise_on_failure=True)
            except Exception as e:
                raise AssertionError(f'The codomain has an error: {e}')

class AffineHomeomorphism(Element):
    r'''
    EXAMPLES::

        sage: from pet_salon import PolytopeUnions
        sage: U = PolytopeUnions(2, QQ)
        sage: p0 = Polyhedron(vertices=[(0,0), (1,0), (0,1)])
        sage: p1 = Polyhedron(vertices=[(1,0), (1,1), (0,1)])
        sage: domain = U({0: p0, 1: p1})
        sage: domain
        Disjoint union of 2 nonoverlapping polyhedra in QQ^2
        sage: Aff = U.affine_group()
        sage: a0 = Aff([[1, 1], [0, 1]])
        sage: a0
              [1 1]     [0]
        x |-> [0 1] x + [0]
        sage: a1 = Aff([[0, -1], [1, 0]], [1, 0])
        sage: A = U.affine_homeomorphisms()
        sage: A
        Collection of label-respecting affine homeomorphisms of disjoint unions of 2-dimensional polytopes defined over Rational Field
        sage: f = A(domain, {0: a0, 1: a1}, codomain_is_nonoverlapping=True)
        sage: TestSuite(f).run()
        sage: f(domain.point(0, (1/4, 1/3)))
        Point(0, (7/12, 1/3))
    '''
    def __init__(self, parent, domain, affine_mapping, codomain=None, codomain_is_nonoverlapping=None):
        self._domain = domain
        if length(affine_mapping) < infinity:
            G = parent.affine_group()
            self._affine_mapping = frozendict({label: G(g) for label, g in affine_mapping.items()})
        else:
            self._affine_mapping = affine_mapping
        if codomain:
            self._codomain = codomain
        else:
            assert codomain_is_nonoverlapping is not None, 'If a codomain is not provided, we require a boolean  `codomain_is_nonoverlapping` which will determine if the codomain is nonoverlapping'
            U = PolytopeUnions(
                parent.dimension(),
                parent.field(),
                finite=domain.is_finite(),
                nonoverlapping = codomain_is_nonoverlapping)
            self._codomain = U(
                function_mapping(domain.labels(),
                lambda label: self._affine_mapping[label]*domain.polytope(label))
            )
        Element.__init__(self, parent)
        self.rename(f'Affine homeomorphism between disjoint unions of {length(domain.labels())} polytopes')

    def domain(self):
        return self._domain

    def codomain(self):
        return self._codomain

    def affine_mapping(self):
        r'''
        Return a mapping sending labels to the corresponding element of the affine group
        '''
        return self._affine_mapping

    def __invert__(self):
        return self.parent()(
            self.codomain(),
            function_mapping(self.domain().labels(), lambda label: ~self._affine_mapping[label]),
            self.domain())

    def __eq__(self, other):
        if self is other:
            return True
        if not hasattr(other, 'parent') or not callable(other.parent) or self.parent() != other.parent():
            return False
        return self.domain() == other.domain() and \
               self.codomain() == other.codomain() and \
               self.affine_mapping() == other.affine_mapping()

    def __hash__(self):
        return hash((self.domain(), self.codomain(), self.affine_mapping()))

    def _mul_(self, other):
        return self.parent()(other.domain(), # domain
           function_mapping(self.domain().labels(), lambda label: self.affine_mapping()[label]*other.affine_mapping()[label]),
           self.codomain()) # codomain

    def _act_on_(self, other, self_on_left):
        #print('Called act on with', self, other, self_on_left)
        if self_on_left:
            if hasattr(other, 'parent') and hasattr(other.parent(), 'category'):
                cat = other.parent().category()
                if cat.is_subcategory(PartitionsCategory()):
                    if self.domain() != other.codomain():
                        raise ValueError('To compose a partition with an affine homeomoprhism the domain and codomain must match')
                    parent = PiecewiseAffineMaps(self.parent().dimension(), self.parent().field())
                    SE = SurjectiveEmbeddings(self.codomain())
                    return parent(other, self, SE())
                PAMs = self.parent().piecewise_affine_maps()
                if PAMs.has_coerce_map_from(other.parent()):
                    return PAMs(self) * PAMs(other)

class AffineHomeomorphisms(UniqueRepresentation, Parent):
    r'''
    Parent for affine homeomorphisms between polytope unions.
    '''
    Element = AffineHomeomorphism

    def __init__(self, dimension, field):
        self._dimension = dimension
        self._field = field
        Parent.__init__(self, category=AffineHomeomorphismsCategory())
        self.rename(f'Collection of label-respecting affine homeomorphisms of disjoint unions of {dimension}-dimensional polytopes defined over {field}')

    def field(self):
        return self._field

    def dimension(self):
        return self._dimension

    def trivial_affine_homeomorphism(self, union):
        r'''Return the trivial affine homeomorphism of union into union.'''
        one = self.affine_group().one()
        return self(union, function_mapping(union.labels(), lambda x: one), codomain=union)

    def _element_constructor_(self, *args, **kwds):
        return self.element_class(self, *args, **kwds)

# PIECEWISE AFFINE

def _reverse_order_p_ah(p, a):
    r'''
    Given a pair of a affine homeomorphism $a$ and a partition $p$ representing the composition $p \circ a$,
    we return a new pair $(a_2, p_2)$ such that $a_2 \circ p_2 = p \circ a$. Here $a_2$ is an affine homeomorphism
    and $p_2$ is a partition.
    '''
    X = a.domain()
    Y = a.codomain()
    assert Y == p.domain(), 'The composition p∘a is not well-defined.'
    Z = p.codomain()
    Y2 = X.parent()(function_mapping(
        Z.labels(),
        lambda label: (~a.affine_mapping()[p.ambient_labels()[label]])*Z.polytope(label)))
    P = Partitions(a.domain())
    p2 = P(Y2, p.ambient_labels())
    AH = a.parent()
    a2 = AH(
        Y2, # domain
        function_mapping(Y2.labels(), lambda label: a.affine_mapping()[p.ambient_labels()[label]]),
        Z)  # codomain
    return (a2, p2)

def _reverse_order_ah_i(a, i):
    r'''
    Given a pair of a affine homeomorphism $a$ and an immersion $i$ representing the composition $a \circ i$,
    we return a new pair $(i_2, a_2)$ such that $i_2 \circ a_2 = a \circ i$. Here $a_2$ is an affine homeomorphism
    and $i_2$ is an immersion.
    '''
    X = i.domain()
    Y = i.codomain()
    assert Y == a.domain(), 'The composition a∘i is not well-defined.'
    Z = a.codomain()
    Y2 = X.parent()(function_mapping(
        X.labels(),
        lambda label: (a.affine_mapping()[i.ambient_labels()[label]])*X.polytope(label)))
    AH = a.parent()
    a2 = AH(
        X, # domain
        function_mapping(X.labels(), lambda label: a.affine_mapping()[i.ambient_labels()[label]]),
        Y2)  # codomain
    I = i.parent().with_different_union(Z)
    i2 = I(Y2, i.ambient_labels())
    return (i2, a2)

def _reverse_order_p_i(p, i):
    r'''
    Given a pair of a parition $p$ and an immersion $i$ representing the composition $p \circ i$,
    we return a new pair $(i_2, p_2)$ such that $i_2 \circ p_2 = p \circ i$. Here $p_2$ is a parition
    and $i_2$ is an immersion of the same type as $i$.
    '''
    # TODO: This only works when the unions are finite!
    X = i.domain()
    Y = i.codomain()
    assert Y == p.domain(), 'The composition p∘i is not well-defined.'
    Z = p.codomain()
    assert X.is_finite() and Z.is_finite(), 'Currently doesn\'t work for the infinite case.'
    relabeler = Relabeler()
    Y2_polytopes = {}
    ambient_labels1 = {}
    ambient_labels2 = {}
    subunions1 = {}
    subunion_parent = X.parent().with_different_axioms(
        finite = X.is_finite() and Z.is_finite(),
        nonoverlapping=True)
    for b in Y.labels():
        for a,x in i.subunions()[b].polytopes().items():
            subunion_data1 = {}
            subunion_data2 = {}
            for c,z in p.subunions()[b].polytopes().items():
                y2 = x.intersection(z)
                if y2.volume() > 0:
                    b2 = relabeler.new_label((a,c))
                    Y2_polytopes[b2] = y2
                    ambient_labels1[b2] = a
                    ambient_labels2[b2] = c
                    subunion_data1[b2] = y2
            subunions1[a] = subunion_parent(subunion_data1)
    Y2 = X.parent().with_different_axioms(finite = X.is_finite() and Z.is_finite())(Y2_polytopes)
    p2 = Partitions(X)(Y2, ambient_labels1, subunions1)
    I = i.parent().with_different_union(Z)
    i2 = I(Y2, ambient_labels2)
    return (i2, p2)

class PiecewiseAffineMapsCategory(Category):
    r'''The category of (label respecting) affine homeomorphisms between polytope unions.'''
    def __init__(self, *args, **options):
        Category.__init__(self, *args, **options)
        self.rename(f'Category of piecewise affine maps between polytope unions')

    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.
        """
        return [Sets()]

    class SubcategoryMethods:
        pass

    class ParentMethods:

        @abstract_method
        def field(self):
            pass

        @abstract_method
        def dimension(self):
            pass

        def affine_group(self):
            return AffineGroup(self.dimension(), self.field())

        def affine_homeomorphisms(self):
            return AffineHomeomorphisms(self.dimension(), self.field())

        def _coerce_map_from_(self, parent):
            r'''
            EXAMPLES::

            Test of various coercions and operations:

                sage: from pet_salon.pam_examples import integer_multiplication
                sage: im = integer_multiplication(2, QQ, 2)
                sage: im
                Multiplication by 2 in the 2-torus defined over Rational Field
                sage: p = im.partition()
                sage: a = im.affine_homeomorphism()
                sage: i = im.immersion()
                sage: p.parent()
                Partitions of 2-cube
                sage: PAMs = im.parent()
                sage: PAMs
                Collection of piecewise affine maps between disjoint unions of 2-dimensional polytopes defined over Rational Field
                sage: PAMs.has_coerce_map_from(a.parent())
                True
                sage: aa = PAMs(a)
                sage: TestSuite(aa).run()
                sage: aa
                Piecewise affine map from 4 small 2-cubes to disjoint union of 4 polyhedra in QQ^2
                sage: PAMs.has_coerce_map_from(p.parent())
                True
                sage: pp = PAMs(p)
                sage: TestSuite(pp).run()
                sage: pp
                Piecewise affine map from 2-cube to 4 small 2-cubes
                sage: PAMs.has_coerce_map_from(i.parent())
                True
                sage: ii = PAMs(i)
                sage: TestSuite(ii).run()
                sage: ii
                Piecewise affine map from disjoint union of 4 polyhedra in QQ^2 to 2-cube
                sage: a.parent()
                Collection of label-respecting affine homeomorphisms of disjoint unions of 2-dimensional polytopes defined over Rational Field
                sage: f = a*p
                sage: TestSuite(f).run()
                sage: f
                Piecewise affine map from 2-cube to disjoint union of 4 polyhedra in QQ^2
                sage: g = i*a
                sage: TestSuite(g).run()
                sage: g
                Piecewise affine map from 4 small 2-cubes to 2-cube
                sage: h = p*i
                sage: TestSuite(h).run()
                sage: h
                Piecewise affine map from disjoint union of 4 polyhedra in QQ^2 to 4 small 2-cubes
            '''
            if not hasattr(parent,'category'):
                return False
            cat = parent.category()
            if cat.is_subcategory(PiecewiseAffineMapsCategory()) or \
               cat.is_subcategory(AffineHomeomorphismsCategory()) or \
               cat.is_subcategory(ImmersionsCategory()) or \
               cat.is_subcategory(PartitionsCategory()):
                return self.dimension() == parent.dimension() and \
                       self.field().has_coerce_map_from(parent.field())

    class ElementMethods:

        @abstract_method
        def partition(self):
            r'''The domain partition for the map. This is the first step of the map.'''
            pass

        @abstract_method
        def affine_homeomorphism(self):
            r'''The affine homeomorphism between the partitions. This is the second step of the map.'''
            pass

        @abstract_method
        def immersion(self):
            r'''The immersion for the map. This is the third step of the map.'''
            pass

        @cached_method
        def domain(self):
            r'''The domain for the map: A polytope union.'''
            return self.partition().domain()

        @cached_method
        def codomain(self):
            r'''The domain for the map: A polytope union.'''
            return self.immersion().codomain()

        def is_injective(self):
            r'''Return `True` if the map is injective. `False` if not.'''
            return 'Injective' in self.immersion().parent().category().axioms()

        def is_surjective(self):
            r'''Return `True` if the map is surjective. `False` if not.'''
            return 'Surjective' in self.immersion().parent().category().axioms()

        def __call__(self, x):
            r'''Return the image of x under the mapping.'''
            point1 = self.partition()(x)
            point2 = self.affine_homeomorphism()(point1)
            return self.immersion()(point2)

        def _test_composition(self, tester=None):
            r'''A piecewise affine map is a composition of three other maps. This checks if the domains and codomains
            agree ensuring that the composition is well defined.'''
            assert self.partition().codomain() == self.affine_homeomorphism().domain(), \
                'The codomain of the partition must be the domain of the affine homeomorphism'
            assert self.affine_homeomorphism().codomain() == self.immersion().domain(), \
                'The codomain of the affine homeomorphism must be the domain of the immersion.'

        def _test_pieces(self, tester=None):
            r'''Check the three maps defining the PET.'''
            try:
                TestSuite(self.partition()).run(catch=False, raise_on_failure=True)
            except Exception as e:
                raise AssertionError(f'The partition has an error: {e}')
            try:
                TestSuite(self.affine_homeomorphism()).run(catch=False, raise_on_failure=True)
            except Exception as e:
                raise AssertionError(f'The affine homeomorphism has an error: {e}')
            try:
                TestSuite(self.immersion()).run(catch=False, raise_on_failure=True)
            except Exception as e:
                raise AssertionError(f'The immersion has an error: {e}')


class PiecewiseAffineMap(Element):
    def __init__(self, parent, partition, affine_homeomorphism, immersion, name=None):
        self._partition = partition
        self._affine_homeomorphism = affine_homeomorphism
        self._immersion = immersion
        Element.__init__(self, parent)
        if name:
            self.rename(str(name))
        else:
            domain = repr(self.domain())
            codomain = repr(self.codomain())
            self.rename(f'Piecewise affine map from {domain[0].lower()}{domain[1:]} to {codomain[0].lower()}{codomain[1:]}')

    def partition(self):
        r'''The domain partition for the map.'''
        return self._partition

    def affine_homeomorphism(self):
        r'''The affine homeomorphism between the partitions.'''
        return self._affine_homeomorphism

    def immersion(self):
        r'''The domain partition for the map.'''
        return self._immersion

    def _mul_(self, other):
        p1 = other.partition()
        a1 = other.affine_homeomorphism()
        i1 = other.immersion()
        p2 = self.partition()
        a2 = self.affine_homeomorphism()
        i2 = self.immersion()
        # We are looking at i2 * a2 * p2 * i1 * a1 * p1
        # We pass pairs through each other, preserving the product.
        i3, p3 = _reverse_order_p_i(p2, i1)
        # Now it is         i2 * a2 * i3 * p3 * a1 * p1
        a3, p4 = _reverse_order_p_ah(p3, a1)
        # Now it is         i2 * a2 * i3 * a3 * p4 * p1
        i4, a4 = _reverse_order_ah_i(a2, i3)
        # Now it is         i2 * i4 * a4 * a3 * p4 * p1
        i = i2*i4
        a = a4*a3
        #print('p4',p4)
        #print('p4 domain',p4.domain(), 'codomain', p4.codomain())
        #print('p1',p1)
        #print('p1 domain',p1.domain(), 'codomain', p1.codomain())
        #print(p1.codomain() == p4.domain())
        p = p4*p1
        return self.parent()(p, a, i)

    def __invert__(self):
        if not self.immersion().parent().is_injective() and self.immersion().parent().is_surjective():
            raise ValueError('To be an invertible, the PiecewiseAffineMap must have an invertible immersion component.')
        return self.parent(~self.immersion(), ~self.affine_homeomorphism(), ~self.partition())

    def __eq__(self, other):
        if self is other:
            return True
        if hash(self) != hash(other):
            return False
        if not hasattr(other, 'parent') or not callable(other.parent) or self.parent() != other.parent():
            return False
        return self.partition() == other.partition() and \
               self.affine_homeomorphism() == other.affine_homeomorphism() and \
               self.immersion() == other.immersion()

    @cached_method
    def __hash__(self):
        return hash((self.partition(), self.affine_homeomorphism(), self.immersion()))

class PiecewiseAffineMaps(UniqueRepresentation, Parent):
    r'''
    Parent for piecewise affine maps between polytope unions.

    Such a piecewise affine map is a composition of three maps:

    * First, a partition is applied to the domain polytope union, cutting the polytopes into subpolytopes. This is the only source of discontinuity.
    * Second, an affine homeomorphism is applied (sending the subpolytopes to their images under an affine transformation depending on the subpolytope).
    * Third, an immersion is applied sending the images of the subpolytopes into the codomain polytope union.
    '''
    Element = PiecewiseAffineMap

    def __init__(self, dimension, field):
        self._dimension = dimension
        self._field = field
        Parent.__init__(self, category=PiecewiseAffineMapsCategory())
        self.rename(f'Collection of piecewise affine maps between disjoint unions of {dimension}-dimensional polytopes defined over {field}')

    def field(self):
        return self._field

    def dimension(self):
        return self._dimension

    def _element_constructor_(self, *args, **kwds):
        if len(args) == 1:
            if hasattr(args[0], 'parent') and hasattr(args[0].parent(),'category'):
                if args[0].parent().category().is_subcategory(PartitionsCategory()):
                    codomain = args[0].codomain()
                    return self.element_class(self,
                                              args[0],
                                              codomain.parent().affine_homeomorphisms().trivial_affine_homeomorphism(codomain),
                                              SurjectiveEmbeddings(codomain)(), **kwds)
                if args[0].parent().category().is_subcategory(AffineHomeomorphismsCategory()):
                    domain = args[0].domain()
                    P = Partitions(domain)
                    codomain = args[0].codomain()
                    return self.element_class(self,
                                              P(),
                                              args[0],
                                              SurjectiveEmbeddings(codomain)(), **kwds)
                if args[0].parent().category().is_subcategory(ImmersionsCategory()):
                    domain = args[0].domain()
                    P = Partitions(domain)
                    return self.element_class(self,
                                              P(),
                                              domain.parent().affine_homeomorphisms().trivial_affine_homeomorphism(domain),
                                              args[0], **kwds)
        return self.element_class(self, *args, **kwds)

    def _an_element_(self):
        from .pam_examples import integer_multiplication
        # Return multiplication by 2 (mod 1):
        return integer_multiplication(self.dimension(), self.field(), 2)

