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
'''This module contains classes related to points in a `PolytopeUnion`.'''

from sage.categories.all import Sets
from sage.categories.category import Category
from sage.misc.cachefunc import cached_method
from sage.misc.abstract_method import abstract_method
from sage.modules.free_module import VectorSpace
from sage.structure.element import Element
from sage.structure.parent import Parent
from sage.structure.richcmp import (op_EQ, op_NE)
from sage.structure.unique_representation import UniqueRepresentation

from pet_salon.union import PolytopeUnionsCategory

class PointSetsCategory(Category):
    r"""
    The category of points in a `PolytopeUnion`.

    EXAMPLES::

        sage: from pet_salon.point import PointSetsCategory
        sage: PointSetsCategory()
        Category of points in polytope unions
    """
    def __init__(self, *args, **options):
        Category.__init__(self, *args, **options)
        self.rename(f'Category of points in polytope unions')

    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.

        EXAMPLES::

            sage: from pet_salon.point import PointSetsCategory
            sage: C = PointSetsCategory()
            sage: C.super_categories()
            [Category of sets]

        """
        return [Sets()]

    class ParentMethods:

        @abstract_method
        def union(self):
            pass

        def dimension(self):
            return self.union().parent().dimension()

        def field(self):
            return self.union().parent().field()

        @cached_method
        def vector_space(self):
            r'''
            Return the vector space over the provided field of the provided dimension.
            '''
            return VectorSpace(self.field(), self.dimension())

        def center(self, label):
            p = self.union().polytope(label)
            return self(label, p.center())

        def _an_element_(self):
            union = self.union()
            for label in union.labels():
                break
            return self.center(label)

    class ElementMethods:
        def _test_containment(self, tester=None):
            r'''Assert that the point is positioned within the polyhedron with the given label'''
            assert self.position() in self.parent().union().polytope(self.label())

class Point(Element):
    def __init__(self, parent, label, position):
        self._label = label
        self._position = parent.vector_space()(position)
        self._position.set_immutable()
        Element.__init__(self, parent)

    def label(self):
        r'''Return the label of the polytope containing this point.'''
        return self._label

    def position(self):
        r'''Return the position of this point.'''
        return self._position

    def _repr_(self):
        return f'Point({self.label()}, {self.position()})'

    def __hash__(self):
        return hash((self.label(), self.position()))

    def _richcmp_(self, other, op):
        if op!=op_EQ and op!=op_NE:
            return NotImplemented
        if self is other:
            return op == op_EQ
        if not hasattr(other, 'parent') or not callable(other.parent):
            return op == op_NE
        if self.parent() != other.parent():
            return op == op_NE
        if self.label() != other.label():
            return op == op_NE
        return (op == op_EQ) == (self.position() == other.position())

class PointSet(UniqueRepresentation, Parent):
    r'''
    Represents the set of points in a `PolytopeUnion`.

    EXAMPLES::

        sage: from pet_salon import PolytopeUnions
        sage: U = PolytopeUnions(2, QQ, finite=True)
        sage: union = U.an_element()
        sage: union
        Disjoint union of 2 nonoverlapping polyhedra in QQ^2
        sage: PS = union.point_set()
        sage: PS
        Set of points in disjoint union of 2 nonoverlapping polyhedra in QQ^2
        sage: TestSuite(PS).run()
        sage: PS.center(0)
        Point(0, (0, 0))
        sage: pt = PS.center(1)
        sage: pt
        Point(1, (2, 0))
        sage: TestSuite(pt).run()
    '''
    Element = Point

    def __init__(self, union):
        assert union.parent().category().is_subcategory(PolytopeUnionsCategory()), \
            'union must be a PolytopeUnion'
        Parent.__init__(self, category=PointSetsCategory())
        self._union = union
        union_name = repr(union)
        self.rename(f'Set of points in {union_name[0].lower()}{union_name[1:]}')

    def union(self):
        '''Return the `PolytopeUnion` that contains the points.'''
        return self._union

    def __hash__(self):
        return hash((self.category(), self.union()))

    def _element_constructor_(self, *args, **kwds):
        if len(args) == 1:
            return self.element_class(self, args[0].label(), args[0].position(), **kwds)
        if len(args) == 2:
            return self.element_class(self, *args, **kwds)

