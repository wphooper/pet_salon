r"""
**pet_salon:** Polytope Exchange Transformations in [SageMath](https://www.sagemath.org/).
"""
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

from pet_salon.affine import AffineHomeomorphisms
from pet_salon.affine_gps.affine_group import AffineGroup
from pet_salon.immersion import Immersions, SurjectiveImmersions, Embeddings, SurjectiveEmbeddings, Partitions
from pet_salon.orbit import Orbit, StopCriterion
from pet_salon.polyhedra import rectangle
from pet_salon.union import PolytopeUnions, finite_polytope_union

