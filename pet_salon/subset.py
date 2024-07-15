from sage.categories.all import Sets
from sage.categories.category_types import Category_over_base_ring
from sage.misc.cachefunc import cached_method
from sage.misc.abstract_method import abstract_method
from sage.structure.element import Element
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation

from pet_salon.union import PolytopeUnion, PolytopeUnionsCategory

class SubunionCategory(Category_over_base_ring):
    r"""
    The category of polyhedral subsets together with an embedding in an ambient polyhedral union.
    """
    def __init__(self, *args, **options):
        Category_over_base_ring.__init__(self, *args, **options)
        self.rename(f'Category of subsets of a polytope union over {self.base_ring()}')

    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.

        EXAMPLES::

            sage: from pet_salon.point import PointSetsCategory
            sage: C = PointSetsCategory(QQ)
            sage: C.super_categories()
            [Category of sets]

        """
        return [Sets()]

    class ParentMethods:
        
        @abstract_method
        def ambient_union(self):
            r'''Return the ambient polyhedral union.'''
            pass

    class ElementMethods:

        @abstract_method
        def subunion(self, label=None):
            r'''With no parameters, return the subunion. When a label in the ambient union is provided, 
            return the subunion of polytopes contained within associated polytope.'''
            pass

        @abstract_method
        def ambient_labels(self):
            r'''Return a mapping sending labels in the subunion to labels in the ambient union.'''
            pass

        def inclusion(self, subpt):
            r'''Return the image of the point under the inclusion into the ambient_union.'''
            return self.parent().ambient_union().point(
                self.ambient_labels()[subpt.label()],
                subpt.position()
            )

        def preimage(self, pt, all=False, limit=None):
            r'''
            Given a point in the ambient union, find a corresponding point in the subunion. 
            This method just passes the call to `find` from the appropriate subunion.
            '''
            subunion = self.subunion(pt.label())
            return subunion.find(pt.position)

class Subunion(Element):
    def __init__(self, parent, whole_subunion, ambient_labels_mapping=None, subunion_mapping=None):
        self._whole_subunion = whole_subunion
        if not ambient_labels_mapping:
            assert 'DisjointImages' in parent.ambient_union().parent().category().axioms(),
                'ambient_labels_mapping must be defined if the containing PolytopeUnion does not have disjoint images'
            assert parent.ambient_union().is_finite(),
                'ambient_labels_mapping must be defined if the containing PolytopeUnion is not finite'
            assert whole_subunion.is_finite(),
                'ambient_labels_mapping must be defined if `whole_subunion` is not finite'
            ambient_labels_mapping = {}
            for label, polytope in whole_subunion.polytopes().items():
                center = polytope.center()
                pair = parent.ambient_union().find(center)
                if not pair:
                    raise ValueError(f'The subunion polytope with label {label} is not contained in a polytope from the ambient union.')
                ambient_labels_mapping[label] = pair[0]
        if not subunion_mapping:
            assert whole_subunion.is_finite(),
                'ambient_labels_mapping must be defined if `whole_subunion` is not finite'
            assert parent.ambient_union().is_finite(),
                'ambient_labels_mapping must be defined if the containing PolytopeUnion is not finite'
            ambient_label_to_list = {}
            for label, ambient_label in ambient_labels_mapping.items():
                if ambient_label in ambient_label_to_list:
                    ambient_label_to_list[ambient_label].append(label)
                else:
                    ambient_label_to_list[ambient_label] = [label]
            subunion_mapping = {}
            for ambient_label, lst in ambient_label_to_list.items():
                subunion_mapping[ambient_label] = parent.ambient_union().restrict(lst)
        self._whole_subunion = whole_subunion
        self._ambient_labels_mapping = ambient_labels_mapping
        self._subunion_mapping = subunion_mapping

    def subunion(self, label=None):
        r'''With no parameters, return the subunion. When a label in the ambient union is provided, 
        return the subunion of polytopes contained within associated polytope.'''
        if label is None:
            return self._whole_subunion
        else:
            return self._subunion_mapping[label]

    def ambient_labels(self):
        r'''Return a mapping sending labels in the subunion to labels in the ambient union.'''
        return self._ambient_labels_mapping

    def __eq__(self, other):
        if self is other:
            return True
        if not hasattr(other, 'parent') or not callable(other.parent) or self.parent() != other.parent():
            return False
        if self.subunion() != other.subunion():
            return False
        if 'DisjointImages' in self.parent().union().parent().category().axioms():
            # Nothing more to check
            return True
        try:
            len(self.ambient_labels())
            self_ambient_labels_finite = True
        except TypeError:
            self_ambient_labels_finite = False
        try:
            len(other.ambient_labels())
            other_ambient_labels_finite = True
        except TypeError:
            other_ambient_labels_finite = False
        if self_ambient_labels_finite != other_ambient_labels_finite:
            return False
        self_al = self.ambient_labels()
        other_al = other.ambient_labels()
        if self_ambient_labels_finite:
            for label in self.ambient_labels():
                if self_al[label] != other_al[label]:
                    return False
            return True
        else:
            # hopeless
            return False

    def __ne__(self, other):
        return not self.__eq__(other)

    @cached_method
    def __hash__(self):
        if 'DisjointImages' in self.parent().union().parent().category().axioms():
            return hash((self.parent(), self.subunion()))
        else:
            if self.union().is_finite():
                ambient_labels = frozenset((label,ambient_label) for label,ambient_label in self.ambient_labels().items())
                return hash((self.parent(), self.subunion(), ambient_labels))
            else:
                return id(self)

class Subunions(Parent):
    Element = Subunion

    def __init__(self, ambient_union):
        assert ambient_union.parent().category().is_subcategory(PolytopeUnionsCategory(ambient_union.base_ring())), \
            'ambient_union must be a PolytopeUnion'
        Parent.__init__(self, category=SubunionCategory(ambient_union.base_ring()))
        self._ambient_union = ambient_union
        union_name = repr(ambient_union)
        self.rename(f'Subunions contained in {union_name[0].lower()}{union_name[1:]}')

    def ambient_union(self):
        return self._ambient_union

    def base_ring(self):
        return self.category().base_ring()

    def __eq__(self, other):
        if not hasattr(other, 'category'):
            return False
        if not other.category().is_subcategory(self.category()):
            return False
        return self.ambient_union() == other.ambient_union()

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash((self.category(), self.ambient_union()))

    def trivial(self):
        return self(self.ambient_union(), TrivialSubunion())

    def _element_constructor_(self, *args, **kwds):
        print(f'Called element_constructor with args={args}')
        if len(args)==2:
            if isinstance(args[0], PolytopeUnion):
                if isinstance(args[1], dict):
                    su = FiniteSubunion(args[1])
                    return self.element_class(self, args[0], su)
                if isinstance(args[1], AbstractSubunion):
                    return self.element_class(self, args[0], args[1])
        raise NotImplementedError()

    def _an_element_(self):
        return self.trivial()

