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
from copy import copy

from sage.categories.all import Sets
from sage.categories.category import Category
from sage.categories.category_with_axiom import CategoryWithAxiom, all_axioms
from sage.geometry.polyhedron.parent import Polyhedra
from sage.misc.cachefunc import cached_method
from sage.misc.abstract_method import abstract_method
from sage.modules.free_module import VectorSpace
from sage.rings.infinity import infinity
from sage.structure.element import Element
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation

from pet_salon.collection import length, function_mapping, postcomposition_mapping

# Make Nonoverlapping an axiom in Sage:
all_axioms += ("Nonoverlapping",)

def is_nonoverlapping(polytope_collection):
    assert length(polytope_collection) < infinity, 'is_nonoverlapping only works for finite collections of polytopes!'
    polytopes = list(polytope_collection)
    for i in range(len(polytopes)):
        p1 = polytopes[i]
        for j in range(i+1, len(polytopes)):
            p2 = polytopes[j]
            if p1.intersection(p2).volume() != 0:
                return False
    return True

class PolytopeUnionsCategory(Category):
    r"""
    The category of indexed disjoint unions of polyhedra.

    EXAMPLES::

        sage: from pet_salon.union import PolytopeUnionsCategory
        sage: PolytopeUnionsCategory()
        Category of disjoint polytope unions
    """

    # TODO: Fix category names. Currently
    # PolytopeUnionsCategory().Nonoverlapping().Finite()
    # has a nonsensical name.

    def __init__(self, *args, **options):
        Category.__init__(self, *args, **options)
        self._fix_name()


    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.

        EXAMPLES::

            sage: from pet_salon.union import PolytopeUnionsCategory
            sage: C = PolytopeUnionsCategory()
            sage: C.super_categories()
            [Category of sets]

        """
        return [Sets()]

    class SubcategoryMethods:

        def Nonoverlapping(self):
            r'''We say a PolytopeUnion is *nonoverlapping* if the polytopes, viewed as subsets of the vector space containing them, have disjoint interiors.

            This will make available the `find` method.'''
            return self._with_axiom('Nonoverlapping')

        def _fix_name(self):
            if 'Nonoverlapping' in self.axioms():
                di = 'nonoverlapping '
            else:
                di = ''
            if 'Finite' in self.axioms():
                f = 'finite '
            else:
                f = ''
            self.rename(f'Category of {f}{di}disjoint polytope unions')

    class ParentMethods:
        r"""
        Provides methods available to all subdivisions.

        If you want to add functionality to all subdivisions, independent of
        implementation, you probably want to put it here.
        """

        @abstract_method
        def field(self):
            pass

        @abstract_method
        def dimension(self):
            pass

        def is_finite(self):
            r'''Return `True` if this parent only contains finite objects.

            Return `False` otherwise.
            '''
            return False

        def is_nonoverlapping(self):
            r'''Return `True` if this parent only contains disjoint unions of polytopes that are pairwise disjoint.

            Return `False` otherwise.
            '''
            return False

        @abstract_method
        def with_different_axioms(self, finite=None, nonoverlapping=None):
            pass

        @abstract_method
        def with_different_field(self, new_field):
            pass

        def vector_space(self):
            r'''
            Return the vector space over the provided field of the provided dimension.
            '''
            return VectorSpace(self.field(), self.dimension())

        def polyhedra(self):
            return Polyhedra(self.field(), self.dimension())

        @cached_method
        def point_set_category(self):
            return PointSets(self.field())

        def affine_group(self):
            from pet_salon.affine_gps.affine_group import AffineGroup
            return AffineGroup(self.dimension(), self.field())

        def affine_homeomorphisms(self):
            r'''Return the collection of AffineHomeomorphisms of the same dimension and over the same field.'''
            from pet_salon.affine import AffineHomeomorphisms
            return AffineHomeomorphisms(self.dimension(), self.field())

        def _coerce_map_from_(self, parent):
            r'''
            EXAMPLES::

            Example of coercion:

                sage: from pet_salon import PolytopeUnions
                sage: P_QQ = PolytopeUnions(2, QQ)
                sage: P_QQ
                Finite disjoint unions of nonoverlapping polyhedra in dimension 2 over Rational Field
                sage: P_AA = P_QQ.with_different_field(AA)
                sage: P_AA
                Finite disjoint unions of nonoverlapping polyhedra in dimension 2 over Algebraic Real Field
                sage: P_AA.has_coerce_map_from(P_QQ)
                True
                sage: p = P_AA(P_QQ.an_element())
                sage: p
                Disjoint union of 2 nonoverlapping polyhedra in AA^2
                sage: p.polytope(0).parent()
                Polyhedra in AA^2
            '''
            if not hasattr(parent, 'category'):
                return False
            if not parent.category().is_subcategory(self.category()):
                return False
            if parent.dimension() != self.dimension():
                return False
            return self.field().has_coerce_map_from(parent.field())

    class ElementMethods:
        r"""
        Provides methods available to all subdivisions.

        If you want to add functionality to all subdivisions, independent of
        implementation, you probably want to put it here.
        """
        @abstract_method
        def polytopes(self):
            r'''Return the a mapping from labels to polytopes.'''
            pass

        def labels(self):
            r'''Return the collection of labels.'''
            return self.polytopes().keys()

        def polytope(self, label):
            r'''Return the polytope with the given label.'''
            return self.polytopes()[label]

        def is_finite(self):
            r"""
            Return whether this is a finite subdivision, which it is.
            """
            try:
                len(self.polytopes())
                return True
            except TypeError:
                # len attempts to return infinity which results in an error.
                return False

        def is_nonoverlapping(self):
            return self.parent().is_nonoverlapping()

        @cached_method
        def point_set(self):
            r'''Construct the set of points in this disjoint union'''
            from pet_salon.point import PointSet
            return PointSet(self)

        def point(self, label, position, check=True):
            r'''Construct a points in this disjoint union from a `label` of a polytope and a `position` (vector) within it

            EXAMPLES::

                sage: from pet_salon import PolytopeUnions
                sage: from sage.geometry.polyhedron.constructor import Polyhedron
                sage: U = PolytopeUnions(2, QQ, finite=True)
                sage: union = U(Polyhedron(vertices=[(0,0), (1,0), (0,1)]))
                sage: union.point(0, (1/2, 1/3) )
                Point(0, (1/2, 1/3))
            '''
            pt = self.point_set()(label, position)
            if check:
                try:
                    pt._test_containment()
                except Exception:
                    raise ValueError('position is probably not within polytope')
            return pt

        def restrict(self, new_labels, nonoverlapping=False):
            r'''Return a new PolytopeUnion with a restricted label set but the same polytopes.

            The parameter `new_labels` should be a collection of the new labels.

            The parameter `nonoverlapping` allows you to specify whether the labels have overlaps.

            EXAMPLES::

                sage: from pet_salon import PolytopeUnions, rectangle
                sage: U = PolytopeUnions(2, QQ, finite=True, nonoverlapping=True)
                sage: union = U({
                ....:     0: rectangle(QQ, 0, 1, 0, 1),
                ....:     1: rectangle(QQ, 1, 2, 0, 1),
                ....:     2: rectangle(QQ, 2, 3, 0, 1),
                ....: })
                sage: union
                Disjoint union of 3 nonoverlapping polyhedra in QQ^2
                sage: res = union.restrict([0,2])
                sage: res
                Disjoint union of 2 nonoverlapping polyhedra in QQ^2
                sage: for label in res.labels():
                ....:     print(label, union.polytope(label) == res.polytope(label))
                0 True
                2 True
                sage: TestSuite(res).run()
            '''
            new_dict = function_mapping(new_labels, self.polytope)
            if length(new_dict) < infinity:
                return self.parent().with_different_axioms(finite=True, nonoverlapping = is_nonoverlapping)(new_dict)
            else:
                if nonoverlapping:
                    return self.parent().with_different_axioms(nonoverlapping = is_nonoverlapping)(new_dict)
                else:
                    return self.parent()(new_dict)

        def _test_polytope_parents(self, tester=None, limit=20):
            r'''Check that the union has the correct field for all polytopes.'''
            P = self.parent().polyhedra()
            if self.is_finite():
                for label, p in self.polytopes().items():
                    assert p.parent() == P, f'polytope with label {label} has the wrong parent'
            else:
                for (label, p),_ in zip(self.polytopes().items(), range(limit)):
                    assert p.parent() == P, f'polytope with label {label} has the wrong parent'

        def plot(self, **kwds):
            r'''Plot this polytope union. This only currently works in 2 and 3 dimensions.

            The parameters `polytope_args` and `polytope_kwds` are passed to the `plot_polytope_union`
            function from the `pet_salon.plot` module.

            EXAMPLES::

            A 2-D example:

                sage: from pet_salon import PolytopeUnions
                sage: union = PolytopeUnions(2, QQ).an_element()
                sage: # Random cached colors:
                sage: union.plot() # not tested
                sage: # Colors chosen by label:
                sage: union.plot(polytope_kwds={'fill': {0:'red', 1:'orange'}}) # not tested

            A 3-D example:

                sage: from pet_salon import PolytopeUnions
                sage: union = PolytopeUnions(3, QQ).an_element()
                sage: union.plot(polytope_kwds={'fill': {0:'red', 1:'orange'}}) # not tested
            '''
            from .plot import plot_polytope_union
            return plot_polytope_union(self, **kwds)

    class Finite(CategoryWithAxiom):
        r"""
        The axiom satisfied by finite subdivisions.

        EXAMPLES::

            sage: from pet_salon.union import PolytopeUnionsCategory
            sage: C = PolytopeUnionsCategory()
            sage: C.Finite()
            Category of finite disjoint polytope unions
        """
        def __init__(self, *args, **options):
            CategoryWithAxiom.__init__(self, *args, **options)
            self._fix_name()

        class ParentMethods:
            r"""
            Provides methods available to all parents of finite disjoint unions.
            """

        class ElementMethods:
            r"""
            Provides methods available to all finite disjoint unions.
            """
            def is_finite(self):
                r"""
                Return whether this is a finite subdivision, which it is.
                """
                return True

            @cached_method
            def volume(self, limit=None):
                return sum([p.volume() for _,p in self.polytopes().items()])

            def restrict(self, new_labels, nonoverlapping=False):
                r'''Return a new PolytopeUnion with a restricted label set but the same polytopes.

                The parameter `new_labels` should be a collection of the new labels.

                The parameter `nonoverlapping` allows you to specify whether the labels have overlaps.
                '''
                new_dict = function_mapping(new_labels, self.polytope)
                if nonoverlapping:
                    return self.parent().with_different_axioms(nonoverlapping = is_nonoverlapping)(new_dict)
                else:
                    return self.parent()(new_dict)


    class Nonoverlapping(CategoryWithAxiom):
        r"""
        The axiom satisfied by finite subdivisions.

        EXAMPLES::

            sage: from pet_salon.union import PolytopeUnionsCategory
            sage: C = PolytopeUnionsCategory()
            sage: C.Nonoverlapping()
            Category of nonoverlapping disjoint polytope unions
        """
        def __init__(self, *args, **options):
            CategoryWithAxiom.__init__(self, *args, **options)
            self._fix_name()

        class ParentMethods:

            def is_nonoverlapping(self):
                r'''Return `True` if this parent only contains disjoint unions of polytopes that are pairwise disjoint.

                Return `False` otherwise.
                '''
                return True

        class ElementMethods:
            def _test_for_overlap(self, tester=None, limit=10):
                r'''
                Test that the polytopes have pairwise disjoint interior.

                If the union is finite, we test all pairs for overlap. If the union
                is finite we go up to the `limit` parameter (default: `10`).
                '''
                if self.is_finite():
                    assert is_nonoverlapping(self.polytopes().values()), 'Two polytopes overlap'
                else:
                    polytopes = [p for p,_ in zip(self.polytopes().values(), range(limit))]
                    assert is_nonoverlapping(polytopes), 'Two polytopes overlap'

            def find(self, position, all=False, limit=None):
                r'''
                Find a polytope containing the position (point).

                By default, we return the pair `(label, polytope)` associated to the
                first polytope found containing the point. If none is found `None` is
                returned.

                Since the polytopes only have disjoint interiors, it is possible
                that more than one polytope contains the position. To see all the polytopes,
                set the parameter `all=True`, then instead a generator is returned that
                iterates through all the polytopes containing the point. This option is
                (currently) only possible if the union is finite.

                For infinite unions, there is a `limit` parameter which describes how many
                polytopes to check before giving up. The default limit is available from
                the module level method `get_find_limit()` and can be changed with
                `set_find_limit(new_limit)`.

                The implementation here just iterates through all nonoverlapping polyhedra in the union,
                checking for containment. This method should be overriden by a more
                efficient algorithm in the infinite case and in the case of large
                finite unions.

                EXAMPLES::

                    sage: from pet_salon import PolytopeUnions
                    sage: U = PolytopeUnions(2, QQ, finite=True, nonoverlapping=True)
                    sage: union = U.an_element()
                    sage: pt = union.polytope(0).intersection(union.polytope(1)).center()
                    sage: pt
                    (1, 0)
                    sage: for label,polytope in union.find(pt, all=True):
                    ....:     print(label)
                    0
                    1
                '''
                position = self.parent().vector_space()(position)
                if self.is_finite():
                    if all:
                        def find_all():
                            for pair in self.polytopes().items():
                                if position in pair[1]:
                                    yield pair
                        return find_all()
                    if limit:
                        raise ValueError('In a finite surface we do not allow limits in the find operation.')
                    for pair in self.polytopes().items():
                        if position in pair[1]:
                            return pair
                    return None # Failed to find any polytope containing the position.
                else:
                    if all:
                        raise NotImplemented('Currently can only find all in a finite union.')
                    if not limit:
                        limit = _find_limit
                    for pair,_ in zip(self.polytopes().items(), range(limit)):
                        if position in pair[1]:
                            return pair
                    return None # Failed to find any polytope containing the position within the limit.

            def point(self, label_or_position, position=None, check=True, all=False, limit=None):
                r'''Construct a points in this disjoint union from a `label` of a polytope and a `position` (vector) within it, or simply a position.

                EXAMPLES::

                    sage: from pet_salon import PolytopeUnions
                    sage: U = PolytopeUnions(2, QQ, finite=True, nonoverlapping=True)
                    sage: union = U.an_element()
                    sage: pt = union.polytope(0).intersection(union.polytope(1)).center()
                    sage: pt
                    (1, 0)
                    sage: for pt in union.point(pt, all=True):
                    ....:     print(pt)
                    Point(0, (1, 0))
                    Point(1, (1, 0))
                '''
                if position is None:
                    if all:
                        P = self.point_set()
                        def point_generator():
                            for label,_ in self.find(label_or_position, all=True, limit=limit):
                                yield P(label, label_or_position)
                        return point_generator()
                    else:
                        found = self.find(label_or_position, all=False, limit=limit)
                        if found is None:
                            raise ValueError('The provided coordinates were not within the union.')
                        else:
                            return self.point_set()(found[0], label_or_position)
                else:
                    assert not all, 'If a label and a position are provided, `all` must be False.'
                    pt = self.point_set()(label_or_position, position)
                    if check:
                        try:
                            pt._test_containment()
                        except Exception:
                            raise ValueError('position is probably not within polytope')
                    return pt

            def restrict(self, new_labels, nonoverlapping=False):
                r'''Return a new PolytopeUnion with a restricted label set but the same polytopes.

                The parameter `new_labels` should be a collection of the new labels.

                We ignore the `nonoverlapping` parameter because this union has no overlaps.
                '''
                new_dict = function_mapping(new_labels, self.polytope)
                if length(new_dict) < infinity:
                    return self.parent().with_different_axioms(finite=True)(new_dict)
                else:
                    return self.parent()(new_dict)

        class Finite(CategoryWithAxiom):
            r"""
            The axiom satisfied by finite subdivisions.

            EXAMPLES::

                sage: from pet_salon.union import PolytopeUnionsCategory
                sage: C = PolytopeUnionsCategory()
                sage: C.Finite().Nonoverlapping()
                Category of finite nonoverlapping disjoint polytope unions
            """
            def __init__(self, *args, **options):
                CategoryWithAxiom.__init__(self, *args, **options)
                self._fix_name()

            class ElementMethods:

                def restrict(self, new_labels, nonoverlapping=False):
                    r'''Return a new PolytopeUnion with a restricted label set but the same polytopes.

                    The parameter `new_labels` should be a collection of the new labels.

                    We ignore the `nonoverlapping` parameter because this union has no overlaps.
                    '''
                    new_dict = function_mapping(new_labels, self.polytope)
                    return self.parent()(new_dict)

class PolytopeUnion(Element):
    def __init__(self, parent, mapping, name=None):
        r'''
        Construct a new Polytope union.

        The `parent` should be a `PolytopeUnions`, which specifies the `field`
        as well as the dimension. The mapping should send labels to polyhedra.
        '''
        self._mapping = mapping
        Element.__init__(self, parent)
        if name:
            self.rename(name)
        else:
            s = str(self.parent().polyhedra())
            if self.is_finite():
                size = len(self.polytopes())
            else:
                size = f'∞ly many'
            if 'Nonoverlapping' in self.parent().category().axioms():
                no = 'nonoverlapping '
            else:
                no = ''
            self.rename(f'Disjoint union of {size} {no}{s[0].lower()}{s[1:]}')

    def polytopes(self):
        r'''Return the a mapping from labels to polytopes.'''
        return self._mapping

    def __eq__(self, other):
        if self is other:
            return True
        if not isinstance(other, PolytopeUnion):
            return False
        if self.parent() != other.parent():
            return False
        if self.is_finite() != other.is_finite():
            return False
        return self.polytopes() == other.polytopes()

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        if self.is_finite():
            return hash((self.parent(), frozenset(self.polytopes().items())))
        else:
            hash(id(self))

#    def __repr__(self):
#        s = str(self.parent().polyhedra())
#        if self.is_finite():
#            size = len(self.polytopes())
#            return f'Disjoint union of {size} {s[0].lower()}{s[1:]}'
#        else:
#            return f'Disjoint union of infinitely many {s[0].lower()}{s[1:]}'

class PolytopeUnions(UniqueRepresentation, Parent):
    r'''
    Parent for domains of PETs of a given dimension that are defined over a given field.

    EXAMPLES::

    We can convert a single polyhedron to a union. It creates a union with a label of `0`.

        sage: from pet_salon import PolytopeUnions
        sage: from sage.geometry.polyhedron.constructor import Polyhedron
        sage: U = PolytopeUnions(2, QQ, finite=True)
        sage: TestSuite(U).run()
        sage: p0 = Polyhedron(vertices=[(1,0), (1,1), (-1,2)])
        sage: print(p0)
        A 2-dimensional polyhedron in ZZ^2 defined as the convex hull of 3 vertices
        sage: union = U(p0)
        sage: union
        Disjoint union of 1 nonoverlapping polyhedra in QQ^2
        sage: TestSuite(union).run()
        sage: union.labels()
        dict_keys([0])
        sage: print(union.polytope(0))
        A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices

    An example of an infinite union:

        sage: from collections.abc import Mapping
        sage: from pet_salon import PolytopeUnions
        sage: U = PolytopeUnions(2, QQ, finite=False)
        sage: U
        Disjoint unions of nonoverlapping polyhedra in dimension 2 over Rational Field
        sage: class ZZ2mapping(Mapping):
        ....:     def __init__(self, unions):
        ....:         from sage.rings.integer_ring import ZZ
        ....:         self._ZZ2 = ZZ.cartesian_product(ZZ)
        ....:         self._U = unions
        ....:     def __getitem__(self, key):
        ....:         if key in self._ZZ2:
        ....:             V = self._U.vector_space()
        ....:             v = V([*key]) # Convert to vector (neccessary for elements of ZZ2)
        ....:             return self._U.polyhedra()(Polyhedron(vertices=[v, v+V((1,0)), v+V((0,1)), v+V((1,1))]))
        ....:         else:
        ....:             raise KeyError
        ....:     def __iter__(self):
        ....:         return self._ZZ2.__iter__()
        ....:     def __len__(self):
        ....:         return infinity
        ....:
        sage: mapping = ZZ2mapping(U)
        sage: print(mapping[(3,4)])
        A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 4 vertices
        sage: union = U(mapping)
        sage: union
        Disjoint union of ∞ly many nonoverlapping polyhedra in QQ^2
        sage: TestSuite(union).run(skip=['_test_pickling'])
    '''
    Element = PolytopeUnion

    def __init__(self, dimension, field, finite=True, nonoverlapping=True):
        cat = PolytopeUnionsCategory()
        if finite:
            cat = cat.Finite()
        if nonoverlapping:
            cat = cat.Nonoverlapping()
        Parent.__init__(self, category=cat)
        self._field = field
        self._n = dimension
        if nonoverlapping:
            no = 'nonoverlapping '
        else:
            no = ''
        if finite:
            self.rename(f'Finite disjoint unions of {no}polyhedra in dimension {self._n} over {self.field()}')
        else:
            self.rename(f'Disjoint unions of {no}polyhedra in dimension {self._n} over {self.field()}')

    def field(self):
        r"""
        Return the ring over which this subdivision is defined.
        """
        return self._field

    def dimension(self):
        r'''
        Return the dimension of the domains.
        '''
        return self._n

    def with_different_axioms(self, finite=None, nonoverlapping=None):
        if finite is None:
            finite = self.is_finite()
        if nonoverlapping is None:
            nonoverlapping = self.is_nonoverlapping()
        return PolytopeUnions(self.dimension(), self.field(), finite, nonoverlapping)

    def with_different_field(self, new_field):
        return PolytopeUnions(self.dimension(), new_field, self.is_finite(), self.is_nonoverlapping())

    def __eq__(self, other):
        if not isinstance(other, PolytopeUnions):
            return False
        return self.dimension() == other.dimension() and self.field() == other.field()

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash((self.dimension(), self.field()))

    def find_limit(self):
        if hasattr(self, '_default_find_limit'):
            return self._default_find_limit
        else:
            return 100

    def set_find_limit(self, limit):
        assert limit in ZZ and limit>0, 'limit should be a positive integer'
        self._default_find_limit = limit

    def volume_check_limit(self):
        if hasattr(self, '_volume_check_limit'):
            return self._volume_check_limit
        else:
            return 100

    def set_volume_check_limit(self, limit):
        assert limit in ZZ and limit>0, 'limit should be a positive integer'
        self._volume_check_limit = limit

    def containment_check_limit(self):
        if hasattr(self, '_containment_check_limit'):
            return self._containment_check_limit
        else:
            return 100

    def set_containment_check_limit(self, limit):
        assert limit in ZZ and limit>0, 'limit should be a positive integer'
        self._containment_check_limit = limit

    def intersection_check_limit(self):
        if hasattr(self, '_intersection_check_limit'):
            return self._intersection_check_limit
        else:
            return 20

    def set_intersection_check_limit(self, limit):
        assert limit in ZZ and limit>0, 'limit should be a positive integer'
        self._intersection_check_limit = limit

    def _element_constructor_(self, *args, **kwds):
        #print(f'Called element_constructor with args={args} and kwds={kwds}')
        if len(args)==1:
            if hasattr(args[0],'parent'):
                if args[0].parent() == self:
                    # Conversion unnecessary
                    return args[0]
                if hasattr(args[0].parent(), 'category') and args[0].parent().category().is_subcategory(PolytopeUnionsCategory()):
                    if args[0].parent().field() == self.field():
                        # Don't need to convert the fields, just convert!
                        return self.element_class(self, args[0].polytopes(), **kwds)
                    else:
                        return self.element_class(self,
                                                  postcomposition_mapping(args[0].polytopes(), self.polyhedra()),
                                                  **kwds)
            if isinstance(args[0], Mapping):
                return self.element_class(self,
                                          postcomposition_mapping(args[0], self.polyhedra()),
                                          **kwds)
            else:
                # We assume that the object passed is a Polyhedron
                try:
                    p0 = self.polyhedra()(args[0])
                    return self.element_class(self, {0: p0}, **kwds)
                except TypeError:
                    raise ValueError('Conversion not implemented yet')
        raise ValueError('Unclear how creat a polytope union from the passed parameters')

    def _an_element_(self):
        if 'Nonoverlapping' in self.category().axioms():
            from sage.geometry.polyhedron.library import polytopes
            P = self.polyhedra()
            p0 = P(polytopes.hypercube(self.dimension()))
            v = copy(self.vector_space().zero())
            v[0] = 2
            p1 = P(polytopes.cross_polytope(self.dimension())) + v
            return self({0:p0, 1:p1})
        else:
            from sage.geometry.polyhedron.library import polytopes
            P = self.polyhedra()
            p0 = P(polytopes.hypercube(self.dimension()))
            p1 = P(polytopes.cross_polytope(self.dimension()))
            return self({0:p0, 1:p1})

def finite_polytope_union(dimension, field, mapping, name=None):
    r'''
    Construct a finite polytope union.

    The parameters are the `dimension` $d$, a base `field` $F$, and a dictionary sending labels to polytopes with vertices in $F^d$. If a `name` is provided, the name of the union will be set to this.

    An advantage of this function is that it automatically decides if the polytopes overlap.
    '''
    if is_nonoverlapping(mapping.values()):
        U = PolytopeUnions(dimension, field, finite=True, nonoverlapping=True)
        return U(mapping, name=name)
    else:
        U = PolytopeUnions(dimension, field, finite=True, nonoverlapping=False)
        return U(mapping, name=name)

_find_limit = 100

def get_find_limit():
    r'''Get the limit for number of polytopes to check in a `find` operation in an infinite polyhedral union.'''
    return _find_limit

def set_find_limit(new_limit):
    r'''Set the limit for number of polytopes to check in a `find` operation in an infinite polyhedral union.'''
    global _find_limit
    _find_limit = new_limit



