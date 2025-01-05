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

'''
This module contains classes related to ``PolytopeUnions``, disjoint unions of polytopes.
'''


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
from sage.rings.integer_ring import ZZ
from sage.structure.element import Element
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation

from pet_salon.collection import length, function_mapping, postcomposition_mapping

# Make Nonoverlapping an axiom in Sage:
all_axioms += ("Nonoverlapping",)

def is_nonoverlapping(polytope_collection):
    r'''Return if the polytope collection is non-overlapping.

    We require the collection to be finite.

    Parameters:
    polytope_collection (iterable): A collection of polytopes.

    Returns:
    bool: True if the collection is non-overlapping, False otherwise.

    Raises:
    ValueError: If the collection is infinite.
    '''
    if length(polytope_collection) == infinity:
        raise ValueError('is_nonoverlapping only works for finite collections of polytopes!')
    polytopes = list(polytope_collection)
    for i in range(len(polytopes)):
        p1 = polytopes[i]
        for j in range(i+1, len(polytopes)):
            p2 = polytopes[j]
            if p1.intersection(p2).volume() != 0:
                return False
    return True

_find_limit = 100

def get_find_limit():
    r'''Get the limit for number of polytopes to check in a ``find`` operation in an infinite polyhedral union.'''
    return _find_limit

def set_find_limit(new_limit):
    r'''Set the limit for number of polytopes to check in a ``find`` operation in an infinite polyhedral union.'''
    global _find_limit
    _find_limit = new_limit

class PolytopeUnionsCategory(Category):
    r"""
    The category of indexed disjoint unions of polyhedra.

    EXAMPLES::

        sage: from pet_salon.union import PolytopeUnionsCategory
        sage: PolytopeUnionsCategory()
        Category of disjoint polytope unions
    """
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

            This will make available the ``find`` method.'''
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

        def empty_union(self):
            r'''Return the empty union with this parent.

            EXAMPLES::

                sage: from pet_salon import *
                sage: PU = PolytopeUnions(2, QQ)
                sage: eu = PU.empty_union()
                sage: TestSuite(eu).run()
                sage: eu
                Disjoint union of 0 nonoverlapping polyhedra in QQ^2
            '''
            return self({})

        def is_finite(self):
            r'''Return ``True`` if this parent only contains finite objects.

            Return ``False`` otherwise.
            '''
            return False

        def is_nonoverlapping(self):
            r'''
            Return ``False`` because this collection of polytopes is not known to have pairwise disjoint interiors.
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
            r'''
            Return the parent ``Polyhedra`` over the base field with the same dimension.
            '''
            return Polyhedra(self.field(), self.dimension())

        @cached_method
        def point_set(self):
            r'''
            Return the parent of points in the union.
            '''
            from pet_salon.point import PointSet
            return PointSet(self)

        def affine_group(self):
            r'''
            Return the affine group with the same dimension and base field.
            '''
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
            r'''Return the a mapping (dictionary) sending labels to polytopes.'''
            pass

        def labels(self):
            r'''Return the collection of labels.'''
            return self.polytopes().keys()

        def polytope(self, label):
            r'''Return the polytope with the given label.'''
            return self.polytopes()[label]

        def is_finite(self):
            r"""
            Return whether this is a finite subdivision.
            """
            try:
                len(self.polytopes())
                return True
            except TypeError:
                # len attempts to return infinity which results in an error.
                return False

        def is_nonoverlapping(self):
            r'''Return if the parent is nonoverlapping.'''
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

        def restrict(self, new_labels, nonoverlapping=False, mapping=False):
            r'''Return a new PolytopeUnion with a restricted label set but the same polytopes.

            The parameter ``new_labels`` should be a collection of the new labels.

            The parameter ``nonoverlapping`` allows you to specify whether the labels have overlaps.

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
            if mapping:
                from pet_salon.immersion import Embeddings
                e = Embeddings(self)
                return e.restriction(new_labels, nonoverlapping=nonoverlapping)
            else:
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

            The parameters ``polytope_args`` and ``polytope_kwds`` are passed to the ``plot_polytope_union``
            function from the ``pet_salon.plot`` module.

            A 2-D example::

                sage: from pet_salon import PolytopeUnions
                sage: union = PolytopeUnions(2, QQ).an_element()
                sage: # Random cached colors:
                sage: union.plot() # not tested
                sage: # Colors chosen by label:
                sage: union.plot(polytope_kwds={'fill': {0:'red', 1:'orange'}}) # not tested

            A 3-D example::

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

            def union(self, union_list, disjoint=False, mappings=False, check=True):
                r'''
                Return the union of multiple PolytopeUnions, included in `union_list`.

                If `disjoint` is set to `True`, then we take a disjoint union instead of a
                regular union. In this case, the polytopes we take a union of are relabeled:
                `old_label` becomes the pair `(i, old_label)` where `i` is the index in the
                union_list.

                By default `disjoint` is `False`. In this case, an error will occur if two
                labels from different PolytopeUnions correspond to different polytopes.

                If `mappings` is set to True, instead we return the list of inclusions of the
                PolytopeUnions into their union.

                The result will be an object with this class as the parent. Note that the union
                of nonoverlapping polytope unions is not necessarily nonoverlapping. If `check` is
                `True` (the default) and this class represents nonoverlapping polytopes, we check to
                see if the polytopes in the list are all nonoverlapping and we check that the
                resulting union is nonoverlapping.

                EXAMPLES::

                    sage: from pet_salon import *
                    sage: PU = PolytopeUnions(2, QQ)
                    sage: PU
                    Finite disjoint unions of nonoverlapping polyhedra in dimension 2 over Rational Field
                    sage: square0 = PU({0:rectangle(QQ, 0, 2, 0, 2)})
                    sage: square0
                    Disjoint union of 1 nonoverlapping polyhedra in QQ^2
                    sage: square1 = PU({1:rectangle(QQ, 1, 3, 1, 3)})
                    sage: square1
                    Disjoint union of 1 nonoverlapping polyhedra in QQ^2
                    sage: PU.union([square0, square1])
                    Traceback (most recent call last):
                    ...
                    ValueError: The union is overlapping (but this parent represents nonoverlapping PolytopeUnions).

                    sage: from pet_salon import *
                    sage: PU = PolytopeUnions(2, QQ)
                    sage: square0 = PU({0:rectangle(QQ, 0, 2, 0, 2)})
                    sage: square1 = PU({1:rectangle(QQ, 1, 3, 1, 3)})
                    sage: PUO = PolytopeUnions(2, QQ, nonoverlapping=False)
                    sage: pu = PUO.union([square0, square1])
                    sage: pu
                    Disjoint union of 2 polyhedra in QQ^2
                    sage: TestSuite(pu).run()
                    sage: PUO.union([square0, square1], mappings=True)
                    [Embedding of disjoint union of 1 polyhedra in QQ^2 into disjoint union of 2 polyhedra in QQ^2,
                     Embedding of disjoint union of 1 polyhedra in QQ^2 into disjoint union of 2 polyhedra in QQ^2]
                '''
                try:
                    if len(union_list) < 2:
                        raise ValueError('Union only defined for at least two PolytopeUnions.')
                except TypeError:
                    raise ValueError('The first parameter to `union()` must be a list of PolytopeUnions.')
                if not disjoint:
                    if check and self.is_nonoverlapping():
                        for another in union_list:
                            if not another.is_nonoverlapping():
                                raise ValueError('In order for a union to be nonoverlapping, the pieces must also be nonoverlapping.')

                    # Convert into the same parent.
                    union_list = [self(x) for x in union_list]

                    d = copy(union_list[0].polytopes())
                    for another in union_list[1:]:
                        for label, polytope in another.polytopes().items():
                            if label in d and d[label] != polytope:
                                raise ValueError(f'Two unions have label {label} but different polytopes.')
                            else:
                                d[label] = polytope
                    if check and self.is_nonoverlapping():
                        if not is_nonoverlapping(d.values()):
                            raise ValueError(f'The union is overlapping (but this parent represents nonoverlapping PolytopeUnions).')
                    union = self(d)
                    if not mappings:
                        return union
                    maps = []
                    for another in union_list:
                        maps.append( union.restrict(another.labels(), mapping=True) )
                    return maps
                else:
                    # This is the disjoint case.
                    if not mappings:
                        relabeled_unions = []
                        for i, u in enumerate(union_list):
                            relabel_dict = {}
                            for label in u.labels():
                                relabel_dict[label] = (i, label)
                            relabeled_unions.append(u.relabel(relabel_dict))

                        ret = self.union(relabeled_unions, check=check)
                        return ret
                    relabel_maps = []
                    for i, u in enumerate(union_list):
                        relabel_dict = {}
                        for label in u.labels():
                            relabel_dict[label] = (i, label)
                        relabel_maps.append(u.relabel(relabel_dict, mapping=True))

                    codomains = [m.codomain() for m in relabel_maps]
                    maps_into_the_union = self.union(codomains, mappings=True, check=check)
                    compositions = []
                    for i in range(len(union_list)):
                        compositions.append( maps_into_the_union[i]*relabel_maps[i] )
                    return compositions

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
                r'''
                Calculate the total volume of the collection of polytopes.

                This method iterates through all polytopes in the collection and sums their individual volumes.

                :param limit: (Optional) A parameter to limit the calculation. Currently not used in the implementation.
                :type limit: Any
                :return: The total volume of all polytopes in the collection.
                :rtype: Element in the base field
                '''
                return sum([p.volume() for _,p in self.polytopes().items()])

            def restrict(self, new_labels, nonoverlapping=False, mapping=False):
                r'''Return a new PolytopeUnion with a restricted label set but the same polytopes.

                The parameter ``new_labels`` should be a collection of the new labels.

                The parameter ``nonoverlapping`` allows you to specify whether the polytopes associated to the new_labels have overlaps.

                If ``mapping`` is set to ``True`` then an embedding will be returned rather than the union.

                EXAMPLES::

                    sage: from pet_salon import *
                    sage: two_squares = finite_polytope_union(2, QQ, {
                    ....:     0 : rectangle(QQ, 0, 1, 0, 1),
                    ....:     1 : rectangle(QQ, 0, 1, 0, 1),
                    ....: })
                    sage: two_squares.restrict([1], nonoverlapping=True, mapping=True)
                    Embedding of disjoint union of 1 nonoverlapping polyhedra in QQ^2 into disjoint union of 2 polyhedra in QQ^2
                '''
                if mapping:
                    from pet_salon.immersion import Embeddings
                    e = Embeddings(self)
                    return e.restriction(new_labels, nonoverlapping=nonoverlapping)
                else:
                    new_dict = function_mapping(new_labels, self.polytope)
                    if nonoverlapping:
                        return self.parent().with_different_axioms(nonoverlapping = nonoverlapping)(new_dict)
                    else:
                        return self.parent()(new_dict)

            def relabel(self, relabel_dict, mapping = False):
                r'''
                Relabel this Polytope union according to the dictionary `relabel_dict` which maps current
                labels to the new new labels.

                If `mapping` is true, then we construct the surjective embedding from the the current
                polytope union to the relabeled union.

                TODO: Support infinite unions.

                EXAMPLES::

                    sage: from pet_salon import *
                    sage: from pet_salon.pam_examples import quadrilateral_map
                    sage: f = quadrilateral_map(QQ, (2,3/2))
                    sage: codomain = f.codomain()
                    sage: relabeled_codomain = codomain.relabel({0:2})
                    sage: relabeled_codomain
                    Disjoint union of 1 nonoverlapping polyhedra in QQ^2
                    sage: list(relabeled_codomain.labels())
                    [2]
                    sage: relabeled_mapping = codomain.relabel({0:2}, mapping=True)
                    sage: relabeled_mapping.ambient_labels()
                    {0: 2}
                '''
                from pet_salon.immersion import SurjectiveEmbeddings
                new_polytopes = {}
                for label, polytope in self.polytopes().items():
                    new_polytopes[relabel_dict[label]] = polytope
                new_union = self.parent()(new_polytopes)
                if not mapping:
                    return new_union
                se = SurjectiveEmbeddings(new_union)
                return se(self, relabel_dict)

            def canonicalize(self, mapping=False, dictionary=False):
                r'''
                Return a canonical form of the polytope union, this is a new polytope union with the same polytopes but with the labels given by the polytopes themselves. This only works if the polytopes in the union are unique.

                If `mapping` is `True`, then we return the canonical form of the polytope union as an surjective embedding into the canonical form.

                If `dictionary` is `True`, then we just return a dictionary mapping the old labels to the new labels.

                If both `mapping` and `dictionary` are `True`, then we return the dictionary and the surjective embedding.

                Remark: The canonical form may change in the future.

                EXAMPLES::

                    sage: from pet_salon import rectangle, PolytopeUnions
                    sage: PU = PolytopeUnions(2, QQ, finite=True)
                    sage: rect = rectangle(QQ, 0, 1, 0, 1)
                    sage: union = PU({0:rect, 1:rect})
                    sage: union.canonicalize()
                    Traceback (most recent call last):
                    ...
                    ValueError: The polytopes are not unique.
                '''
                if not self.is_finite():
                    raise ValueError('Currently only implemented for finite unions.')
                d = self.polytopes()
                d_reversed = {v:k for k,v in d.items()}
                if len(d) != len(d_reversed):
                    raise ValueError('The polytopes are not unique.')
                if dictionary:
                    if mapping:
                        raise ValueError('Cannot return both a dictionary and a mapping.')
                    return d
                return self.relabel(d, mapping=mapping)

            def union(self, another, mappings=False, disjoint=False, nonoverlapping=False, check=True):
                r'''
                Construct the union of this PolytopeUnion with another PolytopeUnion.

                If `disjoint` is set to `True`, then we relabel the polytopes: `old_label` is changed to
                `(i, old_label)` where `i` is `0` for polytopes in self, and `1` for polytopes in another.

                If `disjoint` is set to `False`: If the unions share a common label, then they must refer
                to the same polygon. (Otherwise a ValueError is raised.)

                If `mappings` is false (the default) we return the union. Otherwise we return the pair of
                inclusions into the union.

                Note that the union of nonoverlapping PolytopeUnions may be overlapping. By default the returned
                PolytopeUnion is assumed to be overlapping. To declare it nonoverlapping set `nonoverlapping=True`.
                In this case, by default we check to make sure the result is nonoverlapping. To disable this behavior,
                set `check=False`.

                EXAMPLES::

                    sage: from pet_salon import *
                    sage: two_squares = finite_polytope_union(2, QQ, {
                    ....:     0 : rectangle(QQ, 0, 2, 0, 2),
                    ....:     1 : rectangle(QQ, 1, 3, 1, 3),
                    ....: })
                    sage: square_and_rectangle = finite_polytope_union(2, QQ, {
                    ....:     0 : rectangle(QQ, 0, 2, 0, 2),
                    ....:     2 : rectangle(QQ, 2, 4, 0, 1),
                    ....: })
                    sage: u = two_squares.union(square_and_rectangle)
                    sage: u
                    Disjoint union of 3 polyhedra in QQ^2
                    sage: f,g = two_squares.union(square_and_rectangle, mappings=True)
                    sage: f.domain() == two_squares and g.domain() == square_and_rectangle
                    True
                    sage: u == f.codomain() == g.codomain()
                    True

                    sage: from pet_salon import *
                    sage: two_squares = finite_polytope_union(2, QQ, {
                    ....:     0 : rectangle(QQ, 0, 2, 0, 2),
                    ....:     1 : rectangle(QQ, 1, 3, 1, 3),
                    ....: })
                    sage: square_and_rectangle = finite_polytope_union(2, QQ, {
                    ....:     0 : rectangle(QQ, 0, 2, 0, 2),
                    ....:     2 : rectangle(QQ, 2, 4, 0, 1),
                    ....: })
                    sage: u = two_squares.union(square_and_rectangle, disjoint=True)
                    sage: u
                    Disjoint union of 4 polyhedra in QQ^2
                    sage: f,g = two_squares.union(square_and_rectangle, mappings=True, disjoint=True)
                    sage: f.domain() == two_squares and g.domain() == square_and_rectangle
                    True
                    sage: u == f.codomain() == g.codomain()
                    True

                '''
                parent = self.parent().with_different_axioms(nonoverlapping=nonoverlapping)
                return parent.union([self, another], disjoint=disjoint, mappings=mappings, check=check)
#                d = copy(self.polytopes())
#                for label, polytope in another.polytopes().items():
#                    if label in d and d[label] != polytope:
#                        raise ValueError(f'The two union both have label {label} but the polytopes are different.')
#                    else:
#                        d[label] = polytope
#                union = self.parent()(d)
#                if not mappings:
#                    return union
#                first_map = union.restrict(self.labels(), mapping=True)
#                second_map = union.restrict(another.labels(), mapping=True)
#                return (first_map, second_map)

#            def disjoint_union(self, another, mappings=False):
#                r'''
#                Construct the disjoint union of this PolytopeUnion with another PolytopeUnion.

#                If `mappings` is False we return the union. Otherwise we return the pair of inclusions into the union.

#                EXAMPLES::

#                '''
#                parent = self.parent().with_different_axioms(nonoverlapping=nonoverlapping)
#                return parent.union([self, another], mappings=mappings, check=check)
#                if not mappings:
#                    relabel_self_dict = {}
#                    for label in self.labels():
#                        relabel_self_dict[label] = (0, label)
#                    relabeled_self = self.relabel(relabel_self_dict)

#                    relabel_another_dict = {}
#                    for label in another.labels():
#                        relabel_another_dict[label] = (1, label)
#                    relabeled_another = another.relabel(relabel_another_dict)

#                    du = relabeled_self.union(relabeled_another)
#                    return du
#                relabel_self_dict = {}
#                for label in self.labels():
#                    relabel_self_dict[label] = (0, label)
#                relabeled_self_map = self.relabel(relabel_self_dict, mapping=True)

#                relabel_another_dict = {}
#                for label in another.labels():
#                    relabel_another_dict[label] = (1, label)
#                relabeled_another_map = another.relabel(relabel_another_dict, mapping=True)

#                self_inc, another_inc = relabeled_self_map.codomain().union(relabeled_another_map.codomain(), mappings=True)
#                return (self_inc*relabeled_self_map, another_inc*relabeled_another_map)

    class Nonoverlapping(CategoryWithAxiom):
        r"""
        The axiom satisfied by polytope unions with disjoint interiors.

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
                r'''Return ``True`` if this parent only contains disjoint unions of polytopes that are pairwise disjoint.

                Return ``False`` otherwise.
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

                By default, we return the pair ``(label, polytope)`` associated to the
                first polytope found containing the point. If none is found ``None`` is
                returned.

                Since the polytopes only have disjoint interiors, it is possible
                that more than one polytope contains the position. To see all the polytopes,
                set the parameter ``all=True``, then instead a generator is returned that
                iterates through all the polytopes containing the point. This option is
                (currently) only possible if the union is finite.

                For infinite unions, there is a ``limit`` parameter which describes how many
                polytopes to check before giving up. The default limit is available from
                the module level method ``get_find_limit()`` and can be changed with
                ``set_find_limit(new_limit)``.

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
                        limit = get_find_limit()
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

            def restrict(self, new_labels, nonoverlapping=False, mapping=True):
                r'''Return a new PolytopeUnion with a restricted label set but the same polytopes.

                The parameter ``new_labels`` should be a collection of the new labels.

                We ignore the ``nonoverlapping`` parameter because this union has no overlaps.
                '''
                if mapping:
                    from pet_salon.immersion import Embeddings
                    e = Embeddings(self)
                    return e.restriction(new_labels, nonoverlapping=nonoverlapping)
                else:
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

                def restrict(self, new_labels, nonoverlapping=False, mapping=False):
                    r'''Return a new PolytopeUnion with a restricted label set but the same polytopes.

                    The parameter `new_labels` should be a collection of the new labels.

                    We ignore the `nonoverlapping` parameter because this union has no overlaps.
                    '''
                    if mapping:
                        from pet_salon.immersion import Embeddings
                        e = Embeddings(self)
                        return e.restriction(new_labels, nonoverlapping=nonoverlapping)
                    else:
                        new_dict = function_mapping(new_labels, self.polytope)
                        return self.parent()(new_dict)



class PolytopeUnion(Element):
    def __init__(self, parent, mapping, name=None):
        r'''
        Construct a new Polytope union.

        The ``parent`` should be a ``PolytopeUnions``, which specifies the ``field``
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

    To construct a PolytopeUnions, call with a ``dimension`` and a ``field``. Keyword parameters include ``finite``
    and ``nonoverlapping`` which should be either true or false. These keywords determine the category.

    To construct a PolytopeUnion from a PolytopeUnions object ``U``, you use
    ```python
    union = U(polytopes_mapping)
    ```
    where ``polytopes_mapping`` is a mapping sending labels to polytopes (of the right dimension).

    We can convert a single polyhedron to a union. It creates a union with a label of ``0``::

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

    Constructing a finite polytope union::

        sage: from pet_salon import PolytopeUnions, rectangle
        sage: pu = PolytopeUnions(2, AA, finite=True, nonoverlapping=False)
        sage: p = pu({   0: rectangle(QQ, 0, 1, 0, 1),     # [0,1] x [0,1]
        ....:          'a': rectangle(QQ, 1/2, 1, 1/2, 2) # [1/2, 1] x [1/2, 1]
        ....:        })
        sage: p
        Disjoint union of 2 polyhedra in AA^2
        sage: print(p.polytope('a'))
        A 2-dimensional polyhedron in AA^2 defined as the convex hull of 4 vertices

    An example of an infinite union::

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
    """
    Construct a finite polytope union.

    Parameters:
    dimension (int): The dimension of the polytopes.
    field (field): The base field where the vertices of the polytopes lie.
    mapping (dict): A dictionary mapping labels to polytopes with vertices in `F^d`.
    name (str, optional): The name of the union. Defaults to None.

    Returns:
    PolytopeUnions: An instance of PolytopeUnions representing the union of the given polytopes.

    Notes:
    This function automatically determines if the polytopes overlap and constructs the union accordingly.
    """
    if is_nonoverlapping(mapping.values()):
        U = PolytopeUnions(dimension, field, finite=True, nonoverlapping=True)
        return U(mapping, name=name)
    else:
        U = PolytopeUnions(dimension, field, finite=True, nonoverlapping=False)
        return U(mapping, name=name)