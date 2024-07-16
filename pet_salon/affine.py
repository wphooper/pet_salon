from collections.abc import Mapping

from sage.categories.all import Sets
from sage.categories.category import Category
from sage.groups.affine_gps.affine_group import AffineGroup
from sage.misc.abstract_method import abstract_method
from sage.misc.cachefunc import cached_method
from sage.misc.sage_unittest import TestSuite
from sage.rings.infinity import infinity
from sage.structure.element import Element
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation

from pet_salon.collection import identity_mapping, function_mapping, length
from pet_salon.immersion import Immersions, Partitions
from pet_salon.union import PolytopeUnions

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

        def affine_group(self):
            return AffineGroup(self.dimension(), self.field())

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
                sage: f = A(domain, {0: a}, codomain_has_disjoint_images=True)
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
                Disjoint union of 2 polyhedra in QQ^2
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
                sage: f = A(domain, {0: a0, 1: a1}, codomain_has_disjoint_images=True)
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
        Disjoint union of 2 polyhedra in QQ^2
        sage: Aff = U.affine_group()
        sage: a0 = Aff([[1, 1], [0, 1]])
        sage: a0
              [1 1]     [0]
        x |-> [0 1] x + [0]
        sage: a1 = Aff([[0, -1], [1, 0]], [1, 0])
        sage: A = U.affine_homeomorphisms()
        sage: A
        Collection of label-respecting affine homeomorphisms of disjoint unions of 2-dimensional polytopes defined over Rational Field
        sage: f = A(domain, {0: a0, 1: a1}, codomain_has_disjoint_images=True)
        sage: TestSuite(f).run()
        sage: f(domain.point(0, (1/4, 1/3)))
        Point(0, (7/12, 1/3))
    '''
    def __init__(self, parent, domain, affine_mapping, codomain=None, codomain_has_disjoint_images=None):
        self._domain = domain
        self._affine_mapping = affine_mapping
        if codomain:
            self._codomain = codomain
        else:
            assert codomain_has_disjoint_images is not None, 'If a codomain is not provided, we require a boolean  `codomain_has_disjoint_images` which will determine if the codomain has the `disjoint_images` property.'
            U = PolytopeUnions(
                parent.dimension(),
                parent.field(),
                finite=domain.is_finite(),
                disjoint_images = codomain_has_disjoint_images)
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

    def _element_constructor_(self, *args, **kwds):
        return self.element_class(self, *args, **kwds)

# PIECEWISE AFFINE

class PiecewiseAffineMapCategory(Category):
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

    class ElementMethods:

        @cached_method
        def domain(self):
            r'''The domain for the map: A polytope union.'''
            return self.domain_partition().parent().ambient_union()

        @abstract_method
        def domain_partition(self):
            r'''The domain partition for the map.'''
            pass

        @abstract_method
        def affine_homeomorphism(self):
            r'''The affine homeomorphism between the partitions.'''
            pass

        @abstract_method
        def codomain_immersion(self):
            r'''The domain partition for the map.'''
            pass


        @abstract_method
        def affine_mapping(self):

        @abstract_method
        def codomain(self):
            r'''The codomain for the map: A polytope union.'''
            pass



