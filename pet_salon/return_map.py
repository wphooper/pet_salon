from pet_salon import Embeddings, PolytopeUnions, SurjectiveEmbeddings, AffineHomeomorphisms, Immersions
from sage.misc.cachefunc import cached_method
from copy import copy

class ReturnMap:
    def __init__(self, f, return_labels):
        '''Constructing the first return map to the union of polytopes with labels in
        the list `return_labels`.'''
        assert f.domain().is_finite(), 'Return maps are only defined for maps with finite domains.'
        assert f.domain()==f.codomain(), 'Return maps are only defined for self maps.'
        return_labels = frozenset(return_labels)
        all_labels = set(f.domain().labels())
        assert all_labels.issuperset(return_labels), 'return labels should be a subset of all labels of f.'
        other_labels = frozenset(all_labels.difference(return_labels))

        X = f.domain()
        I = X.restrict(return_labels, mapping=True)
        #J = X.restrict(other_labels, mapping=True)

        # We are trying to construct the "union" of f_restricted and the identity I.
        #f_restricted = f*J
        f_restricted = f.restriction(other_labels)

        # We need to relabel the domain of I when including...
        f_part = f.partition()
        new_labels = {}
        for label in return_labels:
            new_labels[label] = next(iter(f_part.subunion(label).labels()))
        old_labels = {new_label:old_label for old_label,new_label in new_labels.items()}

        A = I.domain()
        A_prime = A.relabel(new_labels)

        # Names of polytope unions related to f_restricted
        A_c = f_restricted.domain()
        B = f_restricted.partition().codomain()
        C = f_restricted.affine_homeomorphism().codomain()

        B_prime = B.union(A_prime)
        C_prime = C.union(A_prime)

        PAMs = f.parent()
        AH = PAMs.affine_homeomorphisms()
        AG = PAMs.affine_group()

        # Combining the affine homeomorphisms
        f_restricted_ah = f_restricted.affine_homeomorphism()
        new_affine_mapping = copy(f_restricted_ah.affine_mapping())
        for new_label in old_labels:
            new_affine_mapping[new_label] = AG.one()
        ah = AH(B_prime, new_affine_mapping)
        # Sanity check
        assert ah.codomain() == C_prime, 'These should be the same: bug!'

        # Combining the affine immersions
        f_restricted_imm = f_restricted.immersion()
        new_ambient_labels = copy(f_restricted_imm.ambient_labels())
        for old_label, new_label in new_labels.items():
            new_ambient_labels[new_label]=old_label
        IX = Immersions(X)
        new_imm = IX(C_prime, new_ambient_labels)

        f_restricted_part = f_restricted.partition()
        new_ambient_labels2 = copy(f_restricted_part.ambient_labels())
        for old_label, new_label in new_labels.items():
            new_ambient_labels2[new_label]=old_label
        SE = SurjectiveEmbeddings(X)
        new_part = ~ SE(B_prime, new_ambient_labels2)

        # This is the combination of f_restrict and I
        G = new_imm*ah*new_part
        # The following is f restricted to A
        f_A = f*I

        # Store some important objects
        self._G = G
        self._f_A = f_A
        self._return_labels = return_labels
        #self._other_labels = other_labels

    def return_labels(self):
        """Return a frozenset containing the collection of labels we return to."""
        return self._return_labels

    def approximate(self, n):
        '''Return the map which applies f up to n times to points in the the domain of
        the return map. After the first application, we only apply f to points that are
        not in the domain of the return map.'''
        if n==1:
            return self._f_A
        else:
            return self._G**(n-1)*self._f_A

    def get_return_map(self, limit):
        '''
        Either returns `(True, return_map)` or `(False, approximate)` with `n=limit`.
        '''
        approx = self.approximate(limit)
        imm = approx.immersion()
        image_labels = set(imm.subunion_labels())
        if image_labels.issubset(self._return_labels):
            # make the approximate into a return map
            codomain = imm.codomain()
            new_codomain = codomain.restrict(self._return_labels)
            # TODO: The return map is not always a surjective embedding!
            SE = SurjectiveEmbeddings(new_codomain)
            new_imm = SE(imm.domain(), imm.ambient_labels(), imm.subunion_labels())
            return_map = new_imm * approx.affine_homeomorphism() * approx.partition()
            return (True, return_map)
        else:
            return (False, approx)