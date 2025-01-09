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

from collections.abc import Mapping, Collection
from frozendict import frozendict

from sage.categories.all import Sets
from sage.categories.category import Category
from sage.categories.category_with_axiom import CategoryWithAxiom, all_axioms
from sage.misc.abstract_method import abstract_method
from sage.misc.cachefunc import cached_method
from sage.misc.sage_unittest import TestSuite
from sage.plot.plot import graphics_array
from sage.rings.infinity import infinity
from sage.structure.element import Element
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation

from .collection import identity_mapping, function_mapping, length, mapping_composition, tuple_singleton
from .polytope import is_subpolytope
from .union import PolytopeUnions, PolytopeUnionsCategory

# Make 'Injective' and 'Surjective' axioms in Sage:
all_axioms += ('Injective', 'Surjective')

class ImmersionsCategory(Category):
    r"""
    The category of polyhedral subsets together with an embedding in an ambient polyhedral union.

    EXAMPLES::

        sage: from pet_salon.immersion import ImmersionsCategory
        sage: ImmersionsCategory()
        Category of immersions into a polytope union
    """
    def __init__(self, *args, **options):
        Category.__init__(self, *args, **options)
        self.rename(f'Category of immersions into a polytope union')

    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.

        EXAMPLES::

            sage: from pet_salon.immersion import ImmersionsCategory
            sage: C = ImmersionsCategory()
            sage: C.super_categories()
            [Category of sets]
        """
        return [Sets()]

    class SubcategoryMethods:

        def Injective(self):
            r'''Return this category with 'Injective' added to the axioms.

            An immersion is injective if it is one-to-one when restricted to the interior of the polytopes.

            EXAMPLES::

                sage: from pet_salon.immersion import ImmersionsCategory
                sage: ImmersionsCategory().Injective()
                Category of embeddings into a polytope union
                sage: ImmersionsCategory().Surjective().Injective()
                Category of surjective embeddings into a polytope union
            '''
            return self._with_axiom('Injective')

        def Surjective(self):
            r'''Return this category with 'Surjective' added to the axioms.

            An immersion is injective if it maps onto the ambient polytope union.

            EXAMPLES::

                sage: from pet_salon.immersion import ImmersionsCategory
                sage: ImmersionsCategory().Surjective()
                Category of surjective immersions into a polytope union
                sage: ImmersionsCategory().Injective().Surjective()
                Category of surjective embeddings into a polytope union
            '''
            return self._with_axiom('Surjective')

        def description(self):
            r'''Return a string describing the type of maps'''
            return 'Immersion'

    class ParentMethods:

        @abstract_method
        def ambient_union(self):
            r'''Return the ambient polyhedral union. This is also the codomain of the immersion.'''
            pass

        @abstract_method
        def with_different_axioms(self, injective=None, surjective=None):
            r'''Return a parent with the provided axioms.'''
            pass

        @abstract_method
        def with_different_union(self, new_ambient_union):
            pass

        @abstract_method
        def with_different_field(self, new_field):
            r'''Return the same object but defined over a new bigger field.'''
            pass

        def field(self):
            return self.ambient_union().parent().field()

        def dimension(self):
            return self.ambient_union().parent().dimension()

        def is_injective(self):
            return False

        def is_surjective(self):
            return False

        @cached_method
        def polytope_unions(self):
            return PolytopeUnions(self.dimension(), self.field())

        @cached_method
        def piecewise_affine_maps(self):
            from .affine import PiecewiseAffineMaps
            return PiecewiseAffineMaps(self.dimension(), self.field())

        def _coerce_map_from_(self, parent):
            r'''
            EXAMPLES::

            Test coercion and conversion:

                sage: from pet_salon import PolytopeUnions, Immersions, Embeddings
                sage: union = PolytopeUnions(2, QQ).an_element()
                sage: E = Embeddings(union)
                sage: E_AA = E.with_different_field(AA)
                sage: E_AA
                Embeddings into disjoint union of 2 nonoverlapping polyhedra in AA^2
                sage: E_AA.has_coerce_map_from(E)
                True
                sage: e = E.an_element()
                sage: e
                Embedding of disjoint union of 2 nonoverlapping polyhedra in QQ^2 into disjoint union of 2 nonoverlapping polyhedra in QQ^2
                sage: ee = E_AA(e)
                sage: TestSuite(ee).run()
            '''
            if not hasattr(parent, 'category'):
                return False
            if not parent.category().is_subcategory(self.category()):
                return False
            if not self.ambient_union().parent().has_coerce_map_from(parent.ambient_union().parent()):
                return False
            return self.ambient_union().parent()(parent.ambient_union()) == self.ambient_union()

    class ElementMethods:
        @abstract_method
        def domain(self):
            r'''Return the domain of this immersion.'''
            pass

        @abstract_method
        def ambient_labels(self):
            r'''Return a mapping sending labels in the domain to labels in the ambient union.'''
            pass

        @abstract_method
        def subunion_labels(self):
            r'''
            Return a mapping sending an `ambient_label` to the collection of labels that correspond
            to polytopes that map into the polytope with the provided `ambient_label`.

            Warning: We do not require that an `ambient_label` for which there is no polytopes that map in be
            included in the mapping.
            '''
            pass

        @cached_method
        def subunion(self, ambient_label):
            r'''
            Return the restriction of the codomain union to polytopes mapped into the polytope
            with the provided `ambient_label`.
            '''
            try:
                return self.domain().restrict(self.subunion_labels()[ambient_label])
            except KeyError:
                return self.domain().parent().empty_union()

        def codomain(self):
            r'''Return the codomain which is also the ambient union.'''
            return self.parent().ambient_union()

        def __call__(self, subpt):
            r'''Return the image of the point under the inclusion into the ambient_union.

            EXAMPLES::

                sage: from pet_salon.immersion import Immersions
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: U = PolytopeUnions(2, QQ)
                sage: union = U({0: rectangle(QQ,0,1,0,1)})
                sage: S = Immersions(union)
                sage: S
                Immersions into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: su = S(U({1:rectangle(QQ,  0,1/2, 0, 1/2),
                ....:           2:rectangle(QQ,1/2,  1, 0, 1/2),
                ....:          }))
                sage: su
                Immersion of disjoint union of 2 nonoverlapping polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: pt = su.domain().point((2/3,1/4))
                sage: pt
                Point(2, (2/3, 1/4))
                sage: su(pt)
                Point(0, (2/3, 1/4))
            '''
            return self.parent().ambient_union().point(
                self.ambient_labels()[subpt.label()],
                subpt.position()
            )

        def preimage(self, point, all=False, limit=None):
            r'''
            Given a point in the ambient union, find a corresponding point in the domain.

            If `all` is set to `True` we return an iterator over all preimages.

            This method just passes the call to `find` from the appropriate domain.

            EXAMPLES::

                sage: from pet_salon.immersion import Embeddings
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: U = PolytopeUnions(2, QQ)
                sage: union = U({0: rectangle(QQ,0,1,0,1)})
                sage: E = Embeddings(union)
                sage: E
                Embeddings into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: e = E(U({1:rectangle(QQ,  0,1/2, 0, 1/2),
                ....:          2:rectangle(QQ,1/2,  1, 0, 1/2),
                ....:          }))
                sage: e
                Embedding of disjoint union of 2 nonoverlapping polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: pt = union.point((4/5,1/3))
                sage: pt
                Point(0, (4/5, 1/3))
                sage: e.preimage(pt)
                Point(2, (4/5, 1/3))
            '''
            assert point.parent() == self.parent().ambient_union().point_set(), \
                'point must lie in the ambient union'
            subunion = self.subunion(point.label())
            def generator():
                for pt in subunion.point(point.position(), all=all, limit=limit):
                    yield self.domain().point_set()(pt)
            if all:
                return generator()
            else:
                return self.domain().point_set()(subunion.point(point.position()))

        def plot(self, domain_kwds={}, codomain_kwds={}):
            r'''
            Return a `graphics_array` containing plots of the domain and codomain.

            The parameters `domain_kwds` and `codomain_kwds` are passed to the `plot` methods of
            the respective `PolytopeUnion`s.
            '''
            return graphics_array([
                self.domain().plot(**domain_kwds),
                self.codomain().plot(**codomain_kwds)
            ])

        def restriction(self, domain_labels=None, codomain_labels=None, surjective=False):
            r'''Return the restriction of the immersion to a subset of the domain labels.

            If `domain_labels` is provided, then the restriction is to the polytopes with those labels. If `codomain_labels` is provided, then the restriction is to the polytopes in the domain that map into the polytopes with those labels, and the codomain labels are updated accordingly is shrunk to the codomain labels.

            It is not possible to restrict both the domain and codomain labels.

            You may set `surjective` to `True` to declare that the restriction is surjective. This is currently not checked.

            Currently, only restricting the domain labels is implemented.

            EXAMPLES::

                sage: from pet_salon.pam_examples import integer_multiplication
                sage: se =  ~integer_multiplication(2, QQ, 2).partition()
                sage: se
                Surjective embedding of 4 small 2-cubes into 2-cube
                sage: restricted_se = se.restriction([2, 3])
                sage: restricted_se
                Embedding of disjoint union of 2 nonoverlapping polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: list(restricted_se.domain().labels())
                [2, 3]
                sage: se.codomain() == restricted_se.codomain()
                True
                sage: TestSuite(restricted_se).run()
            '''
            if domain_labels:
                if codomain_labels:
                    raise ValueError('Cannot restrict both domain and codomain labels')
                new_parent = self.parent().with_different_axioms(surjective=surjective)
                return new_parent(self.domain().restrict(domain_labels), 
                                {label: self.ambient_labels()[label] for label in domain_labels})
            if codomain_labels:
                raise NotImplementedError('Restricting codomain labels is not implemented yet')

        def _test_containment(self, tester=None):
            r'''Raise an assertion error if a polytope from the domain is not contained within the
            claimed polytope in the ambient union.

            EXAMPLES::

                sage: from pet_salon.immersion import Immersions
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: U = PolytopeUnions(2, QQ)
                sage: union = U({0: rectangle(QQ,0,1,0,1)})
                sage: S = Immersions(union)
                sage: S
                Immersions into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: attempted_subunion = U({1:rectangle(QQ,   0,1/2, 0, 1/2),
                ....:                         2:rectangle(QQ, 1/2,  2, 0, 1/2)})
                sage: attempted_subunion
                Disjoint union of 2 nonoverlapping polyhedra in QQ^2
                sage: su = S(attempted_subunion,
                ....:        { 1: 0, 2: 0},
                ....:        { 0: (1, 2)})
                sage: su
                Immersion of disjoint union of 2 nonoverlapping polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: su._test_containment()
                Traceback (most recent call last):
                ...
                AssertionError...
            '''
            def check_pair(domain_label, ambient_label):
                domain_p = self.domain().polytope(domain_label)
                ambient_p = self.parent().ambient_union().polytope(ambient_label)
                assert is_subpolytope(ambient_p, domain_p), \
                    f'Immersion polytope with label {domain_label} is not contained within ambient polytope with label {ambient_label}'
            if self.domain().parent().is_finite():
                for pair in self.ambient_labels().items():
                    check_pair(*pair)
            else:
                for pair,_ in zip(self.ambient_labels().items(), range(20)):
                    check_pair(*pair)

        def _test_domain(self, tester=None, limit=10):
            r'''Run all PolytopeUnion tests on both the whole domain and the subunions associated to ambient labels.

            EXAMPLES::

                sage: from pet_salon.immersion import Embeddings
                sage: from pet_salon import PolytopeUnions, rectangle
                sage: Udi = PolytopeUnions(2, QQ, nonoverlapping=True)
                sage: U = PolytopeUnions(2, QQ, nonoverlapping=False)
                sage: union = Udi({0: rectangle(QQ,0,1,0,1)})
                sage: E = Embeddings(union)
                sage: E
                Embeddings into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: attempted_subunions = {1: rectangle(QQ,   0,1/2, 0, 1/2),
                ....:                        2: rectangle(QQ,   0,  1, 0, 1/2)}
                sage: su = E(U(attempted_subunions),
                ....:        { 1: 0, 2:0 }, # mapping to ambient label
                ....:        { 0: (1, 2)})
                sage: su
                Embedding of disjoint union of 2 polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                sage: su._test_nonoverlapping()
                sage: su._test_domain()
                Traceback (most recent call last):
                ...
                AssertionError: The subunion associated to ambient label 0 failed a test...
            '''
            try:
                TestSuite(self.domain()).run(catch=False, raise_on_failure=True)
            except Exception as e:
                raise AssertionError(f'The domain failed a test: {e}')
            if length(self.subunion_labels()) < infinity:
                for ambient_label in self.subunion_labels():
                    subunion = self.subunion(ambient_label)
                    try:
                        TestSuite(subunion).run(catch=False, raise_on_failure=True)
                    except Exception as e:
                        raise AssertionError(f'The subunion associated to ambient label {ambient_label} failed a test: {e}')

    class Injective(CategoryWithAxiom):
        def __init__(self, *args, **options):
            CategoryWithAxiom.__init__(self, *args, **options)
            self.rename(f'Category of embeddings into a polytope union')

        class SubcategoryMethods:

            def description(self):
                r'''Return a string describing the type of maps'''
                return 'Embedding'

        class ParentMethods:

            def is_injective(self):
                return True

        class ElementMethods:

            @cached_method
            def subunion(self, ambient_label):
                r'''
                Return a mapping sending an `ambient_label` to the restriction of the subunion to polytopes
                contained within the polytope with the provided `ambient_label`.
                '''
                try:
                    l = self.subunion_labels()[ambient_label]
                except KeyError:
                    l = []
                return self.domain().restrict(l, nonoverlapping=True)

            def _test_nonoverlapping(self, tester=None, limit=20):
                r'''Test that the subunions associated to ambient labels are nonoverlapping.

                This just checks the axiom. The test `_test_subunion` will check that the subunions
                consist of pairwise disjoint polytopes.

                EXAMPLES::

                    sage: from pet_salon.immersion import Embeddings
                    sage: from pet_salon import PolytopeUnions, rectangle
                    sage: U = PolytopeUnions(2, QQ, nonoverlapping=False)
                    sage: union = U({0: rectangle(QQ,0,1,0,1)})
                    sage: E = Embeddings(union)
                    sage: E
                    Embeddings into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                    sage: attempted_domain = U({1:rectangle(QQ,   0, 2/3, 1/4, 3/4),
                    ....:                       2:rectangle(QQ, 1/2,   1, 0, 1/2)})
                    sage: attempted_domain
                    Disjoint union of 2 polyhedra in QQ^2
                    sage: su = E(attempted_domain,
                    ....:        { 1: 0, 2:0 }, # mapping to ambient label
                    ....:        { 0: [1, 2]})
                    sage: su
                    Embedding of disjoint union of 2 polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
                    sage: su._test_nonoverlapping() # Passes because the polytope is falsely declared to be nonoverlapping
                    sage: su._test_domain()
                    Traceback (most recent call last):
                    ...
                    AssertionError: The subunion associated to ambient label 0 failed a test: Two polytopes overlap
                '''
                if length(self.subunion_labels()) < infinity:
                    for ambient_label in self.subunion_labels():
                        subunion = self.subunion(ambient_label)
                        assert subunion.parent().is_nonoverlapping(), \
                            f'The subunion associated to ambient label {ambient_label} is overlapping'
                else:
                    for ambient_label,_ in zip(self.subunion_labels(), range(limit)):
                        subunion = self.subunion(ambient_label)
                        assert subunion.parent().is_nonoverlapping(), \
                            f'The subunion associated to ambient label {ambient_label} is overlapping'

    class Surjective(CategoryWithAxiom):
        def __init__(self, *args, **options):
            CategoryWithAxiom.__init__(self, *args, **options)
            self.rename(f'Category of surjective immersions into a polytope union')

        class SubcategoryMethods:

            def description(self):
                r'''Return a string describing the type of maps'''
                return 'Surjective immersion'

        class ParentMethods:

            def is_surjective(self):
                return True

        class ElementMethods:

            def _test_surjectivity(self, tester=None, limit=20):
                r'''We check surjectivity at the level of the labels.'''
                value = length(self.subunion_labels())
                assert value <= length(self.parent().ambient_union().labels()), \
                    'The mapping is not well defined: There are labels in subunions that do not appear in the ambient union'
                assert value >= length(self.parent().ambient_union().labels()), \
                    'The surjective immersion misses at least one ambient label'
                if value < infinity:
                    assert self.subunion_labels().keys() == self.parent().ambient_union().labels(), \
                        'The support of the subunion mapping is different from the collection of all ambient labels: The sets are different'
                else:
                    for ambient_label,_ in zip(self.parent().ambient_union().labels(), range(limit)):
                        assert ambient_label in self.subunion_labels(), \
                            f'Ambient label {ambient_label} does not appear in the subunion mapping'

            def _test_volume(self, tester=None, limit=20):
                r'''This test checks to see if the subunion of domain polytopes mapping into an ambient
                polytope have volume that is at least as large as the ambient polytope.

                This test only works for finite subunions. If there are infinitely many ambient labels,
                then we test `limit` many.

                EXAMPLES::
                    sage: from pet_salon import PolytopeUnions, rectangle
                    sage: from pet_salon.immersion import SurjectiveEmbeddings
                    sage: U = PolytopeUnions(2, QQ)
                    sage: union = U(rectangle(QQ, 0, 1, 0, 1), name='2-cube')
                    sage: union
                    2-cube
                    sage: P = SurjectiveEmbeddings(union)
                    sage: f = P(U({
                    ....:     1: rectangle(QQ,   0, 1/2,   0, 1/2),
                    ....:     2: rectangle(QQ, 1/2,   1,   0, 1/2),
                    ....:     3: rectangle(QQ,   0, 1/2, 1/2,   1),
                    ....: }))
                    sage: f
                    Surjective embedding of disjoint union of 3 nonoverlapping polyhedra in QQ^2 into 2-cube
                    sage: TestSuite(f).run()
                    Failure in _test_volume:
                    ...
                    The following tests failed: _test_volume
                '''
                def test_pair(ambient_label, subunion):
                    if subunion.is_finite():
                            assert subunion.volume() >= self.parent().ambient_union().polytope(ambient_label).volume(), \
                                f'The surjectivity axiom is violated: The volume of the subunion associated to the ambient label {ambient_label} is not at least as large as the ambient polytope\'s volume'
                if length(self.subunion_labels()) < infinity:
                    for ambient_label in self.subunion_labels():
                        subunion = self.subunion(ambient_label)
                        test_pair(ambient_label, subunion)
                else:
                    for ambient_label,_ in zip(self.subunion_labels(), range(limit)):
                        subunion = self.subunion(ambient_label)
                        test_pair(ambient_label, subunion)

        class Injective(CategoryWithAxiom): # SURJECTIVE EMBEDDINGS
            r'''This is the category of surjective embeddings into a polytope union'''
            def __init__(self, *args, **options):
                CategoryWithAxiom.__init__(self, *args, **options)
                self.rename(f'Category of surjective embeddings into a polytope union')

            class SubcategoryMethods:

                def description(self):
                    r'''Return a string describing the type of maps'''
                    return 'Surjective embedding'

            class ParentMethods:

                def partitions(self):
                    return Partitions(self.ambient_union())

            class ElementMethods:

                def __invert__(self):
                    r'''Return the associated surjective embedding.'''
                    return self.parent().partitions().inverse(self)

                def is_relabeling(self):
                    r'''Return `True` if the surjective embedding is a relabeling. This means that each subunion is a singleton.
                    
                    A relabeling can be converted to a partition.

                    EXAMPLES::
                    
                        sage: from pet_salon import rectangle, PolytopeUnions, Partitions
                        sage: PU = PolytopeUnions(1, QQ)
                        sage: U = PU({0: rectangle(QQ, 0, 1), 1: rectangle(QQ, 1, 2)}, name='U')
                        sage: V = PU({'a': rectangle(QQ, 0, 1), 'b': rectangle(QQ, 1, 2)})
                        sage: emb = U.relabel({0:'a', 1:'b'}, mapping=True)
                        sage: emb.codomain() == V
                        True
                        sage: emb.is_relabeling()
                        True
                        sage: part = Partitions(U)(emb)
                        sage: part
                        Partition of u into 2 subpolytopes
                        sage: part.codomain()==V
                        True
                        sage: part.subunion_labels()
                        {0: ['a'], 1: ['b']}
                    '''
                    if not self.domain().is_finite():
                        raise ValueError('The domain must be finite to check if the surjective embedding is a relabeling')
                    for ambient_label, subunion_labels in self.subunion_labels().items():
                        if len(subunion_labels) != 1:
                            return False
                    return True

class Immersion(Element):
    def __init__(self, parent, domain, ambient_labels_mapping, subunion_labels_mapping, name=None):
        self._domain = domain
        self._ambient_labels_mapping = ambient_labels_mapping
        self._subunion_labels = subunion_labels_mapping
        Element.__init__(self, parent)
        if name:
            self.rename(name)
        else:
            ambient_name = repr(parent.ambient_union())
            start = parent.category().description()
            domain_name = repr(domain)
            self.rename(f'{parent.category().description()} of {domain_name[0].lower()}{domain_name[1:]} into {ambient_name[0].lower()}{ambient_name[1:]}')

# OLD VERSION. PUTTING ALL THE SETUP INTO THE PARENT!
#
#        assert domain.parent().dimension() == parent.dimension(), \
#            'The domain\'s dimension must match the ambient union.'
#        if domain.parent().field() != parent.field():
#            # Attempt to change fields.
#            new_parent = domain.parent().with_different_field(parent.field())
#            domain = new_parent(domain)
#        self._domain = domain
#        if not ambient_labels_mapping:
#            assert 'Nonoverlapping' in parent.ambient_union().parent().category().axioms(), \
#                'ambient_labels_mapping must be defined if the containing PolytopeUnion has overlaps'
#            assert parent.ambient_union().is_finite(), \
#                'ambient_labels_mapping must be defined if the containing PolytopeUnion is not finite'
#            assert domain.is_finite(), \
#                'ambient_labels_mapping must be defined if `domain` is not finite'
#            ambient_labels_mapping = {}
#            for label, polytope in domain.polytopes().items():
#                center = polytope.center()
#                pair = parent.ambient_union().find(center)
#                if not pair:
#                    raise ValueError(f'The subunion polytope with label {label} is not contained in a polytope from the ambient union.')
#                ambient_labels_mapping[label] = pair[0]
#            #print('ambient_labels_mapping', ambient_labels_mapping)
#        self._ambient_labels_mapping = ambient_labels_mapping
#        if not subunion_labels_mapping:
#            assert domain.is_finite(), \
#                'subunions must be defined if `domain` is not finite'
#            assert parent.ambient_union().is_finite(), \
#                'subunions must be defined if the containing PolytopeUnion is not finite'
#            ambient_label_to_list = {}
#            for label, ambient_label in ambient_labels_mapping.items():
#                if ambient_label in ambient_label_to_list:
#                    ambient_label_to_list[ambient_label].append(label)
#                else:
#                    ambient_label_to_list[ambient_label] = [label]
#            subunion_labels_mapping = ambient_label_to_list
#        self._subunion_labels = subunion_labels_mapping
#        Element.__init__(self, parent)
#        if name:
#            self.rename(name)
#        else:
#            ambient_name = repr(parent.ambient_union())
##            axioms = parent.category().axioms()
##            if 'Injective' in axioms and 'Surjective' in axioms:
##                if domain.is_finite():
##                    number = len(domain.polytopes())
##                else:
##                    number = '∞ly many'
##                self.rename(f'Partition of {ambient_name[0].lower()}{ambient_name[1:]} into {number} subpolytopes')
##            else:
#            start = parent.category().description()
#            domain_name = repr(domain)
#            self.rename(f'{parent.category().description()} of {domain_name[0].lower()}{domain_name[1:]} into {ambient_name[0].lower()}{ambient_name[1:]}')

    def domain(self):
        r'''Return the domain of this immersion.'''
        return self._domain

    def subunion_labels(self):
        r'''
        Return a mapping sending an `ambient_label` to the collection of labels that correspond
        to polytopes that map into the polytope with the provided `ambient_label`.
        '''
        return self._subunion_labels

    def ambient_labels(self):
        r'''Return a mapping sending labels in the subunion to labels in the ambient union.'''
        return self._ambient_labels_mapping

    def __eq__(self, other):
        if self is other:
            return True
        if not hasattr(other, 'parent') or not callable(other.parent) or self.parent() != other.parent():
            return False
        if self.domain() != other.domain():
            return False
        if 'Nonoverlapping' in self.parent().ambient_union().parent().category().axioms():
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
        if 'Nonoverlapping' in self.parent().ambient_union().parent().category().axioms():
            return hash((self.parent(), self.domain()))
        else:
            if self.parent().ambient_union().is_finite():
                ambient_labels = frozenset((label,ambient_label) for label,ambient_label in self.ambient_labels().items())
                return hash((self.parent(), self.domain(), ambient_labels))
            else:
                return id(self)

    def _mul_(self, other):
        return self._act_on_(other, True)

    def _act_on_(self, other, self_on_left):
        r'''Implement the action of immersions on other immersions by composition.

        EXAMPLES::
            sage: from pet_salon import rectangle, PolytopeUnions
            sage: U = PolytopeUnions(2, QQ)
            sage: U
            Finite disjoint unions of nonoverlapping polyhedra in dimension 2 over Rational Field
            sage: u1 = U({1: rectangle(QQ, 0, 1, 0, 1)}, name='u1')
            sage: u2 = U({2: rectangle(QQ, 0, 2, 0, 2)}, name='u2')
            sage: u3 = U({3: rectangle(QQ, 0, 3, 0, 3)}, name='u3')
            sage: from pet_salon.immersion import Embeddings
            sage: i12 = Embeddings(u2)(u1) # embedding of u1 into u2
            sage: i23 = Embeddings(u3)(u2) # embedding of u2 into u3
            sage: i13 = Embeddings(u3)(u1) # embedding of u1 into u3
            sage: composition = i23*i12
            sage: composition
            Embedding of u1 into u3
            sage: composition == i13
            True
        '''
        if self_on_left:
            if other.parent and other.parent().category().is_subcategory(ImmersionsCategory()):
                if self.domain() != other.parent().ambient_union():
                    raise ValueError('To compose two immersions, the domain and codomain must be equal')
                injective = 'Injective' in self.parent().category().axioms() and 'Injective' in other.parent().category().axioms()
                surjective = 'Surjective' in self.parent().category().axioms() and 'Surjective' in other.parent().category().axioms()
                parent = self.parent().with_different_axioms(injective, surjective)
                return parent(other.domain(),
                       mapping_composition(self.ambient_labels(), other.ambient_labels()),
                       # We leave it to the constructor to work out the subunions.
                )
            PAMs = self.parent().piecewise_affine_maps()
            if PAMs.has_coerce_map_from(other.parent()):
                return PAMs(self) * PAMs(other)
            #raise ValueError('This left action is not implemented')
        #raise ValueError('Right actions not defined yet')

class Immersions(UniqueRepresentation, Parent):
    r'''
    Collection (parent) of the collection of immersions (or a restricted class of immersions) into a fixed disjoint union of polytopes.

    We call the fixed disjoint union the "ambient union."

    EXAMPLES::

    Construct the trivial SurjectiveEmbedding::

        sage: from pet_salon.immersion import SurjectiveEmbeddings
        sage: from pet_salon import PolytopeUnions
        sage: U = PolytopeUnions(2, QQ)
        sage: union = U.an_element()
        sage: union
        Disjoint union of 2 nonoverlapping polyhedra in QQ^2
        sage: S = SurjectiveEmbeddings(union)
        sage: p = S() # p is the trivial SurjectiveEmbedding
        sage: p
        Surjective embedding of disjoint union of 2 nonoverlapping polyhedra in QQ^2 into disjoint union of 2 nonoverlapping polyhedra in QQ^2
        sage: p.domain() == union
        True
        sage: p.ambient_labels()
        {0: 0, 1: 1}
        sage: pt = p.domain().point((0,0))
        sage: pt
        Point(0, (0, 0))
        sage: pt == p.preimage(pt)
        True
        sage: pt == p(pt)
        True
    '''
    Element = Immersion

    def __init__(self, ambient_union, injective=False, surjective=False):
        assert ambient_union.parent().category().is_subcategory(PolytopeUnionsCategory()), \
            'ambient_union must be a PolytopeUnion'
        cat = ImmersionsCategory()
        start = 'Immersions into'
        if injective:
            start = 'Embeddings into'
            cat = cat.Injective()
        if surjective:
            cat = cat.Surjective()
            if injective:
                start = 'Surjective embeddings into'
            else:
                start = 'Surjective immersions into'
        self._ambient_union = ambient_union
        Parent.__init__(self, category=cat)
        union_name = repr(ambient_union)
        self.rename(f'{start} {union_name[0].lower()}{union_name[1:]}')

    def with_different_axioms(self, injective=None, surjective=None):
        r'''Return a parent with the provided axioms.'''
        if injective is None:
            injective = self.is_injective()
        if surjective is None:
            surjective = self.is_surjective()
        return Immersions(self.ambient_union(), injective=injective, surjective=surjective)

    def with_different_union(self, new_ambient_union):
        r'''Return the same parent but with a different ambient union.'''
        return Immersions(new_ambient_union, self.is_injective(), self.is_surjective())

    def with_different_field(self, new_field):
        r'''Return the same object but defined over a new bigger field.'''
        new_union_parent = self.ambient_union().parent().with_different_field(new_field)
        return Immersions(new_union_parent(self.ambient_union()),
                          self.is_injective(),
                          self.is_surjective())

    def ambient_union(self):
        return self._ambient_union

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

    def restriction(self, ambient_label_collection, nonoverlapping=False):
        if 'Surjective' in self.category().axioms() and ambient_label_collection != self.ambient_union().labels():
            raise ValueError('The only restriction that is surjective is the trivial one')
        U = PolytopeUnions(self.dimension(), self.field(), finite=True, nonoverlapping=True)
        return self.element_class(self,
                                  self.ambient_union().restrict(ambient_label_collection,
                                                                nonoverlapping=nonoverlapping),
                                  identity_mapping(ambient_label_collection),
                                  function_mapping(ambient_label_collection, tuple_singleton))

    def _element_constructor_(self, *args, **kwds):
        #print(f'Called element_constructor with args={args}, len(args)={len(args)}, kwds={kwds}')
        if len(args)==1:
            if hasattr(args[0], 'parent'):
                if args[0].parent() == self:
                    # Just return the element!
                    return args[0]
                if hasattr(args[0].parent(), 'category') and \
                    args[0].parent().category().is_subcategory(ImmersionsCategory()):
                    # It is an immersion.
                    if args[0].parent().field() == self.field():
                        # No field conversion necessary
                        return self.element_class(
                            self,
                            args[0].domain(),
                            args[0].ambient_labels(),
                            args[0].subunion_labels(),
                            **kwds)
                    else:
                        # Convert domain to same parent but with new field
                        U = args[0].domain().parent().with_different_field(self.field())
                        return self.element_class(
                            self,
                            U(args[0].domain()),
                            args[0].ambient_labels(),
                            args[0].subunion_labels(),
                            **kwds)
                # PASS ON ANY OTHER CASE, ESPECIALLY WHERE JUST A POLYTOPE UNION IS PASSED
            if args[0]==0:
                # Construct the trivial immersion
                return self.restriction(self.ambient_union().labels())
        if len(args) <= 3 and hasattr(args[0], 'parent') and hasattr(args[0].parent(), 'category') and \
            args[0].parent().category().is_subcategory(PolytopeUnionsCategory()):

            # Assume the parameters match the first few parameters of the constructor of Immersion.
            domain = args[0]
            assert domain.parent().dimension() == self.dimension(), \
                'The domain\'s dimension must match the ambient union.'
            if domain.parent().field() != self.field():
                # Attempt to change fields.
                new_parent = domain.parent().with_different_field(self.field())
                domain = new_parent(domain)
            # Now domain is setup.
            if len(args) >= 2:
                ambient_labels_mapping = args[1]
                # should be a map between labels
                assert isinstance(ambient_labels_mapping, Mapping), \
                    'The second parameter should be an ambient_labels_mapping, which should be a mapping.'
            else:
                assert self.ambient_union().is_nonoverlapping(), \
                    'ambient_labels_mapping must be defined if the ambient PolytopeUnion has overlaps'
                assert self.ambient_union().is_finite(), \
                    'ambient_labels_mapping must be defined if the containing PolytopeUnion is not finite'
                assert domain.is_finite(), \
                    'ambient_labels_mapping must be defined if `domain` is not finite'
                ambient_labels_mapping = {}
                for label, polytope in domain.polytopes().items():
                    center = polytope.center()
                    pair = self.ambient_union().find(center)
                    if not pair:
                        raise ValueError(f'The subunion polytope with label {label} is not contained in a polytope from the ambient union.')
                    ambient_labels_mapping[label] = pair[0]
            if len(args) >= 3:
                subunion_labels_mapping = args[2]
                assert isinstance(subunion_labels_mapping, Mapping), \
                    'The third parameter should be an subunion_labels_mapping, which should be a mapping.'
                for ambient_label, subunion_labels in subunion_labels_mapping.items():
                    assert isinstance(subunion_labels, Collection), \
                        'The third parameter should be an subunion_labels_mapping, which must be a mapping sending ambient labels to collections of labels in the domain.'
                    break # Just check one
            else:
                assert domain.is_finite(), \
                    'subunions must be defined if `domain` is not finite'
                assert self.ambient_union().is_finite(), \
                    'subunions must be defined if the containing PolytopeUnion is not finite'
                subunion_labels_mapping = {}
                for label, ambient_label in ambient_labels_mapping.items():
                    try:
                        subunion_labels_mapping[ambient_label].append(label)
                    except KeyError:
                        subunion_labels_mapping[ambient_label] = [label]
            return self.element_class(self, domain, ambient_labels_mapping, subunion_labels_mapping, **kwds)
        raise NotImplementedError('Unrecognized information passed to element constructor')

    def _an_element_(self):
        r'''
        TODO: Return an element representative of the parent class.
        '''
        return self()

def SurjectiveImmersions(ambient_union):
    r'''Construct the collection of surjective embedings into the provided ambient union.

    EXAMPLES::

        sage: from pet_salon import PolytopeUnions, rectangle
        sage: from pet_salon.immersion import SurjectiveImmersions
        sage: U = PolytopeUnions(2, QQ)
        sage: union = U(rectangle(QQ, 0, 1, 0, 1), name='2-cube')
        sage: union
        2-cube
        sage: P = SurjectiveImmersions(union)
        sage: P
        Surjective immersions into 2-cube
        sage: TestSuite(P).run()
        sage: V = PolytopeUnions(2, QQ, nonoverlapping=False)
        sage: f = P(V({
        ....:     1: rectangle(QQ,   0, 2/3,   0, 1),
        ....:     2: rectangle(QQ, 1/3,   1,   0, 1),
        ....: }))
        sage: f
        Surjective immersion of disjoint union of 2 polyhedra in QQ^2 into 2-cube
        sage: TestSuite(f).run()
    '''
    return Immersions(ambient_union, injective=False, surjective=True)

def Embeddings(ambient_union):
    r'''Construct the collection of embeddings into the provided ambient union.

    EXAMPLES::

        sage: from pet_salon import PolytopeUnions, rectangle
        sage: from pet_salon.immersion import Embeddings
        sage: U = PolytopeUnions(2, QQ)
        sage: union = U(rectangle(QQ, 0, 1, 0, 1))
        sage: union
        Disjoint union of 1 nonoverlapping polyhedra in QQ^2
        sage: E = Embeddings(union)
        sage: E
        Embeddings into disjoint union of 1 nonoverlapping polyhedra in QQ^2
        sage: TestSuite(E).run()
        sage: e = E(U({
        ....:     1: rectangle(QQ,   0, 1/2,   0, 1/2),
        ....:     2: rectangle(QQ, 1/2,   1,   0, 1/2),
        ....:     3: rectangle(QQ,   0, 1/2, 1/2,   1),
        ....: }))
        sage: e
        Embedding of disjoint union of 3 nonoverlapping polyhedra in QQ^2 into disjoint union of 1 nonoverlapping polyhedra in QQ^2
        sage: TestSuite(e).run()
    '''
    return Immersions(ambient_union, injective=True, surjective=False)

def SurjectiveEmbeddings(ambient_union):
    r'''Construct the collection of surjective embedings into the provided ambient union.

    EXAMPLES::

        sage: from pet_salon import PolytopeUnions, rectangle
        sage: from pet_salon.immersion import SurjectiveEmbeddings
        sage: U = PolytopeUnions(2, QQ)
        sage: union = U(rectangle(QQ, 0, 1, 0, 1), name='2-cube')
        sage: union
        2-cube
        sage: P = SurjectiveEmbeddings(union)
        sage: P
        Surjective embeddings into 2-cube
        sage: TestSuite(P).run()
        sage: f = P(U({
        ....:     1: rectangle(QQ,   0, 1/2,   0, 1/2),
        ....:     2: rectangle(QQ, 1/2,   1,   0, 1/2),
        ....:     3: rectangle(QQ,   0, 1/2, 1/2,   1),
        ....:     4: rectangle(QQ, 1/2,   1, 1/2,   1),
        ....: }))
        sage: f
        Surjective embedding of disjoint union of 4 nonoverlapping polyhedra in QQ^2 into 2-cube
        sage: TestSuite(f).run()
    '''
    return Immersions(ambient_union, injective=True, surjective=True)

class PartitionsCategory(Category):
    r"""
    The category of polyhedral decompositions of an ambient polyhedral union.

    EXAMPLES::

        sage: from pet_salon.immersion import PartitionsCategory
        sage: PartitionsCategory()
        Category of partitions of a polytope union
    """
    def __init__(self, *args, **options):
        Category.__init__(self, *args, **options)
        self.rename(f'Category of partitions of a polytope union')

    def super_categories(self):
        r"""
        Return the categories subdivisions automatically belong to.

        EXAMPLES::

            sage: from pet_salon.immersion import PartitionsCategory
            sage: C = PartitionsCategory()
            sage: C.super_categories()
            [Category of sets]
        """
        return [Sets()]

    class ParentMethods:

        @abstract_method
        def ambient_union(self):
            r'''Return the ambient polyhedral union. This is also the codomain of partitions in the collection viewed as maps.'''
            pass

        def field(self):
            return self.ambient_union().parent().field()

        def dimension(self):
            return self.ambient_union().parent().dimension()

        @cached_method
        def surjective_embeddings(self):
            r'''Return the collection of surjective embeddings into the ambient union.'''
            return SurjectiveEmbeddings(self.ambient_union())

        @cached_method
        def piecewise_affine_maps(self):
            from .affine import PiecewiseAffineMaps
            return PiecewiseAffineMaps(self.dimension(), self.field())

        def with_different_field(self, new_field):
            r'''Return the same object but defined over a new bigger field.'''
            return self.surjective_embeddings().with_different_field(new_field).partitions()

        def _coerce_map_from_(self, parent):
            r'''
            EXAMPLES::

            Example testing coercion and conversion:
            sage: from pet_salon import PolytopeUnions, Partitions
            sage: union = PolytopeUnions(2, QQ).an_element()
            sage: P_QQ = Partitions(union)
            sage: P_AA = P_QQ.with_different_field(AA)
            sage: P_AA
            Partitions of disjoint union of 2 nonoverlapping polyhedra in AA^2
            sage: TestSuite(P_AA).run()
            sage: p = P_QQ.an_element()
            sage: pp = P_AA(p)
            sage: pp
            Partition of disjoint union of 2 nonoverlapping polyhedra in AA^2 into 2 subpolytopes
            sage: TestSuite(pp).run()
            '''
            if not hasattr(parent, 'category'):
                return False
            if not parent.category().is_subcategory(self.category()):
                return False
            if not self.ambient_union().parent().has_coerce_map_from(parent.ambient_union().parent()):
                return False
            return self.ambient_union().parent()(parent.ambient_union()) == self.ambient_union()

    class ElementMethods:

        @abstract_method
        def surjective_embedding(self):
            r'''Return the associated surjective embedding.'''

        def domain(self):
            r''''''
            return self.parent().ambient_union()

        def codomain(self):
            r''''''
            return self.surjective_embedding().domain()

        def subunion_labels(self):
            r'''
            Return a mapping sending an `ambient_label` to the collection of labels of the codomain
            representing the pieces of the polytope with the provided `ambient_label`.
            '''
            return self.surjective_embedding().subunion_labels()

        def subunion(self, ambient_label):
            r'''
            Return the restriction of the codomain subunion to polytopes that the polytope with the
            provided `ambient_label` is divided into.
            '''
            return self.surjective_embedding().subunion(ambient_label)

        def ambient_labels(self):
            r'''Return a mapping sending labels in the subunion to labels in the ambient union.'''
            return self.surjective_embedding().ambient_labels()

        def __invert__(self):
            r'''Return the associated surjective embedding.'''
            return self.surjective_embedding()

        def _test_surjective_embedding(self, tester=None):
            try:
                TestSuite(self.surjective_embedding()).run(catch=False, raise_on_failure=True)
            except Exception as e:
                raise AssertionError(f'The associated surjective embedding failed a test: {e}')

        def restriction(self, labels):
            r'''Return the restriction of the partition to the provided labels.
            
            EXAMPLES::

                sage: from pet_salon.pam_examples import integer_multiplication
                sage: part = integer_multiplication(2, QQ, 2).splitting().partition()
                sage: part
                Partition of 4 small 2-cubes into 16 subpolytopes
                sage: restricted_part = part.restriction([2,3])
                sage: restricted_part
                Partition of disjoint union of 2 nonoverlapping polyhedra in QQ^2 into 8 subpolytopes
                sage: list(restricted_part.domain().labels())
                [2, 3]
                sage: TestSuite(restricted_part).run()
            '''
            new_domain = self.domain().restrict(labels)
            new_codomain_labels = []
            ambient_labels_mapping = {}
            for label in labels:
                temp = self.subunion_labels()[label]
                for codomain_label in temp:
                    ambient_labels_mapping[codomain_label] = label
                new_codomain_labels += temp
            new_codomain = self.codomain().restrict(new_codomain_labels)
            SE = SurjectiveEmbeddings(new_domain)
            se = SE(new_codomain, ambient_labels_mapping)
            return ~se

        def plot(self, domain_kwds={}, codomain_kwds={}):
            r'''
            Return a `graphics_array` containing plots of the domain and codomain.

            The parameters `domain_kwds` and `codomain_kwds` are passed to the `plot` methods of
            the respective `PolytopeUnion`s.
            '''
            return graphics_array([
                self.domain().plot(**domain_kwds),
                self.codomain().plot(**codomain_kwds)
            ])

class Partition(Element):
    def __init__(self, parent, surjective_embedding, name=None):
        # This constructor assumes that the things passed to it are already checked.
        self._surjective_embedding = surjective_embedding
        Element.__init__(self, parent)
        if name:
            name = str(name)
            self.rename(name)
            self._surjective_embedding.rename(f'Surjective embedding associated to {name[0]}{name[1:]}')
        else:
            ambient_name = repr(parent.ambient_union())
            axioms = parent.category().axioms()
            if self.codomain().is_finite():
                number = len(self.codomain().polytopes())
            else:
                number = '∞ly many'
            self.rename(f'Partition of {ambient_name[0].lower()}{ambient_name[1:]} into {number} subpolytopes')

    def surjective_embedding(self):
        r'''Return the associated surjective embedding.'''
        return self._surjective_embedding

    def __eq__(self, other):
        if self is other:
            return True
        if not hasattr(other, 'parent') or not callable(other.parent) or self.parent() != other.parent():
            return False
        return self.surjective_embedding() == other.surjective_embedding()

    def __ne__(self, other):
        return not self.__eq__(other)

    @cached_method
    def __hash__(self):
        return hash((self.parent(), self.surjective_embedding()))

    def __call__(self, pt, **kwds):
        return self.surjective_embedding().preimage(pt, **kwds)

    def _mul_(self, other):
        return self._act_on_(other, True)

    def _act_on_(self, other, self_on_left):
        if self_on_left:
            if other.parent and other.parent().category().is_subcategory(PartitionsCategory()):
                if self.domain() == other.codomain():
                    return ~((~other)*(~self))
            PAMs = self.parent().piecewise_affine_maps()
            if PAMs.has_coerce_map_from(other.parent()):
                return PAMs(self) * PAMs(other)

class Partitions(UniqueRepresentation, Parent):
    r'''
    The collection of partitions of a polytope union.

    EXAMPLES::

        sage: from pet_salon import PolytopeUnions, rectangle
        sage: from pet_salon.immersion import Partitions
        sage: U = PolytopeUnions(2, QQ)
        sage: union = U(rectangle(QQ, 0, 1, 0, 1), name='2-cube')
        sage: union
        2-cube
        sage: P = Partitions(union)
        sage: P
        Partitions of 2-cube
        sage: TestSuite(P).run()
        sage: f = P.inverse(U({
        ....:     1: rectangle(QQ,   0, 1/2,   0, 1/2),
        ....:     2: rectangle(QQ, 1/2,   1,   0, 1/2),
        ....:     3: rectangle(QQ,   0, 1/2, 1/2,   1),
        ....:     4: rectangle(QQ, 1/2,   1, 1/2,   1),
        ....: }))
        sage: f
        Partition of 2-cube into 4 subpolytopes
        sage: TestSuite(f).run()
        sage: f(union.point((1/2,1/3)))
        Point(1, (1/2, 1/3))
    '''
    Element = Partition

    def __init__(self, ambient_union):
        self._ambient_union = ambient_union
        Parent.__init__(self, category=PartitionsCategory())
        union_name = repr(ambient_union)
        self.rename(f'Partitions of {union_name[0].lower()}{union_name[1:]}')

    def ambient_union(self):
        return self._ambient_union

    def __eq__(self, other):
        if not hasattr(other, 'category') or not callable(other.category) or other.category() != self.category():
            return False
        return self.ambient_union() == other.ambient_union()

    def __ne__(self, other):
        return not self.__eq__(other)

    def __hash__(self):
        return hash((self.category(), self.ambient_union()))

    def inverse(self, *args, **kwds):
        r'''
        Construct the partition that is the inverse of a surjective embedding.

        All arguments except the keyword argument `'name'` are passed to the constructor in the parent `self.surjective_embeddings()`. In particular,
        any collection of arguments that produce a surjective embedding can be used here to produce a Partition. The `name` keyword argument is
        passed to the constructor of the partition, allowing it to be provided with a name.
        '''
        if 'name' in kwds:
            name = kwds.pop(name)
        else:
            name = None
        return self.element_class(self, self.surjective_embeddings()(*args, **kwds), name=name)

    def _element_constructor_(self, *args, **kwds):
        '''Construct a partition.'''
        #print(f'Called element_constructor with args={args}')
        if len(args)==1:
            if args[0] == 0:
                # Empty arguments. Construct the trivial partition.
                return self.element_class(self, self.surjective_embeddings()(), **kwds)
            if hasattr(args[0], 'parent') and callable(args[0].parent) and \
                hasattr(args[0].parent(), 'category') and callable(args[0].parent().category):

                if args[0].parent() == self:
                    # Note: Ignoring possible name definition.
                    return args[0]

                if args[0].parent().category().is_subcategory(ImmersionsCategory.Surjective.Injective()):
                    if not args[0].is_relabeling():
                        raise ValueError('The surjective embedding must be a relabeling to convert to a partition.')
                    if args[0].domain() != self.ambient_union():
                        raise ValueError('The domain of the relabeling must match the ambient union.')
                    r = args[0]
                    if not r.domain().is_finite():
                        raise NotImplementedError('The domain must be finite to convert to a partition.')
                    SE = self.surjective_embeddings()
                    d = {ambient_label:subunion_label for subunion_label, ambient_label in r.ambient_labels().items()}
                    return self.element_class(self, SE(r.codomain(), d), **kwds)

                if args[0].parent().category().is_subcategory(PartitionsCategory()):
                    return self.element_class(self, self.surjective_embeddings()(args[0].surjective_embedding()), **kwds)

        raise NotImplementedError('The constructor only works for conversion. Instead use `inverse` to construct from a surjective embedding.')

    def _an_element_(self):
        return self.inverse(self.surjective_embeddings().an_element())

