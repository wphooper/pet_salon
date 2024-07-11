from sage.categories.all import Sets
from sage.categories.category_types import Category_over_base_ring
from sage.categories.category_with_axiom import (
    CategoryWithAxiom_over_base_ring,
    all_axioms,
)
from sage.geometry.polyhedron.parent import Polyhedra
from sage.misc.cachefunc import cached_method
from sage.misc.abstract_method import abstract_method
from sage.modules.free_module import VectorSpace

class Unions(Category_over_base_ring):
    r"""
    The category of indexed disjoint unions of polyhedra.

    EXAMPLES::

        sage: from pet_salon.categories import Subdivisions
        sage: Subdivisions(QQ)
        Category of subdivisions over Rational Field
    """

    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.

        EXAMPLES::

            sage: from pet_salon.categories import Unions
            sage: C = Unions(QQ)
            sage: C.super_categories()
            [Category of sets]

        """
        return [Sets()]

    class ParentMethods:
        r"""
        Provides methods available to all subdivisions.

        If you want to add functionality to all subdivisions, independent of
        implementation, you probably want to put it here.
        """

        @abstract_method
        def dimension(self):
            pass

        def vector_space(self):
            r'''
            Return the vector space over the provided field of the provided dimension.
            '''
            return VectorSpace(self.base_ring(), self.dimension())


        def polyhedra(self):
            return Polyhedra(self.base_ring(), self.dimension())

        @cached_method
        def point_set_category(self):
            return PointSets(self.base_ring())

    class ElementMethods:
        r"""
        Provides methods available to all subdivisions.

        If you want to add functionality to all subdivisions, independent of
        implementation, you probably want to put it here.
        """
        @abstract_method
        def labels(self):
            r'''Return the labels for the collection of subpolyhedra.'''
            pass

        @abstract_method
        def piece(self, label):
            r'''Return the polyhedral piece with the given label.'''
            pass

        def size(self):
            return infinity

        def __repr__(self):
            return f'Disjoint union of {self.size()} polyhedra in {self.parent().polyhedra()}'

        @cached_method
        def point_set(self):
            from pet_salon.union import PointSet
            return PointSet(self)

    class Finite(CategoryWithAxiom_over_base_ring):
        r"""
        The axiom satisfied by finite subdivisions.

        EXAMPLES::

            sage: from pet_salon.categories import Unions
            sage: C = Unions(QQ)
            sage: C.Finite()
            Category of finite unions over Rational Field
        """
        class ParentMethods:
            r"""
            Provides methods available to all finite subdivisions.

            If you want to add functionality to all such subdivisions, you probably
            want to put it here.
            """

        class ElementMethods:
            r"""
            Provides methods available to all finite subdivisions.

            If you want to add functionality to all such subdivisions, you probably
            want to put it here.
            """

            def is_finite(self):
                r"""
                Return whether this is a finite subdivision, which it is.
                """
                return True

            def size(self):
                return len(self.labels())

class PointSets(Category_over_base_ring):
    r"""
    The category of points in a `Union`.
    """

    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.

        EXAMPLES::

            sage: from pet_salon.categories import PointSets
            sage: C = PointSets(QQ)
            sage: C.super_categories()
            [Category of sets]

        """
        return [Sets()]

    class ParentMethods:

        @abstract_method
        def union(self):
            pass

        def dimension(self):
            return self.base().parent().dimension()

        def base_ring(self):
            return self.base().parent().base_ring()

        @cached_method
        def vector_space(self):
            r'''
            Return the vector space over the provided field of the provided dimension.
            '''
            return VectorSpace(self.base_ring(), self.dimension())

        def center(self, label):
            p = self.union().piece(label)
            return self(label, p.center())

        def _an_element_(self):
            union = self.union()
            for label in union.labels():
                break
            return self.center(label)

    class ElementMethods:
        def _test_containment(self, tester=None):
            r'''Assert that the vector is contained within the polyhedron with the given label'''
            assert self.vector() in self.parent().union().piece(self.label())

class Subdivisions(Unions):
    r"""
    The category of (polyhedral) subdivisions of polyhedra defined over a base ring.

    EXAMPLES::

        sage: from pet_salon.categories import Subdivisions
        sage: Subdivisions(QQ)
        Category of subdivisions over Rational Field
    """

    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.

        EXAMPLES::

            sage: from pet_salon.categories import Subdivisions
            sage: C = Subdivisions(QQ)
            sage: C.super_categories()
            [Category of unions over Rational Field]

        """
        return [Unions(self.base_ring())]

    class ParentMethods:
        r"""
        Provides methods available to all subdivisions.

        If you want to add functionality to all subdivisions, independent of
        implementation, you probably want to put it here.
        """
        pass
        
    class ElementMethods:
        r"""
        Provides methods available to all subdivisions.

        If you want to add functionality to all subdivisions, independent of
        implementation, you probably want to put it here.
        """

        @abstract_method
        def polyhedron(self):
            pass

        def _test_containment(self, tester=None, limit=None):
            if limit == None:
                limit = self.parent().containment_check_limit()
            p0 = self.polyhedron()
            for i,label in zip(range(limit), self.labels()):
                p = self.piece(label)
                assert p0.intersection(p) == p, f'Piece with label {label} is not inside the polyhedron'
        
        def _test_volume(self, tester=None, limit=None):
            if limit == None:
                limit = self.parent().volume_check_limit()
            total_volume = self.polyhedron().volume()
            piece_volume = sum([self.piece(label).volume() for i,label in zip(range(limit), self.labels())])
            assert total_volume >= piece_volume, 'The sum of the volumes of the pieces is greater than the volume of the polyhedron.'
            if limit >= self.size():
                assert total_volume <= piece_volume, 'Finite subdivision but the sum of the pieces is less than the total volume.'

        def _test_intersection(self, tester=None, limit=None):
            if limit == None:
                limit = self.parent().intersection_check_limit()
            pieces = [(label, self.piece(label)) for i,label in zip(range(limit), self.labels())]
            for i in range(len(pieces)):
                p = pieces[i][1]
                for j in range(i+1, len(pieces)):
                    assert p.intersection(pieces[j][1]).volume()==0, \
                        'Intersection of piece {pieces[i][0]} with piece {pieces[j][0]} has positive volume'
       
        def find(self, point, all=False, limit=None):
            r'''
            Find the label containing the given point.
            '''
            point = self.parent().vector_space()(point)
            assert point in self.polyhedron(), 'point should be in the polyhedron'
            if not limit:
                if self.size() < infinity:
                    limit = self.size()
                else:
                    limit = self.parent().find_limit()
            if all and self.size()==infinity and limit>100:
                print(f'Warning: we do not check if the subpolygons cover a neighborhood, so this search will run up to the limit {limit}.')
            if all:
                label_list = []
            for i,label in zip(range(limit), self.labels()):
                if point in self.piece(label):
                    if all:
                        label_list.append(label)
                    else:
                        return label
            if all:
                return label_list
            else:
                return None # Failed

        def __repr__(self):
            return f'FiniteSubdivision of {self.polyhedron()} into {self.size()} pieces.'

    class Finite(CategoryWithAxiom_over_base_ring):
        r"""
        The axiom satisfied by finite subdivisions.

        EXAMPLES::

            sage: from pet_salon.categories import Subdivisions
            sage: Subdivisions.Finite(QQ)
            Category of finite subdivisions over Rational Field
        """
        def super_categories(self):
            r"""
            Return the categories subdivisions automatically belong to.

            EXAMPLES::

                sage: from pet_salon.categories import Subdivisions
                sage: C = Subdivisions(QQ)
                sage: C.super_categories()
                [Category of unions over Rational Field]

            """
            return [Subdivisions(self.base_ring()), Unions.Finite(self.base_ring())]


        class ParentMethods:
            r"""
            Provides methods available to all finite subdivisions.

            If you want to add functionality to all such subdivisions, you probably
            want to put it here.
            """
            pass

        class ElementMethods:
            r"""
            Provides methods available to all finite subdivisions.

            If you want to add functionality to all such subdivisions, you probably
            want to put it here.
            """
            pass
