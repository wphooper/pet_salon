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

def is_subpolytope(polytope, potential_subpolytope):
    r'''Return `True` if `potential_subpolytope` is contained in `polytope`.
    Return `False` otherwise.

    This function checks to see if all the vertices of `potential_subpolytope`
    are contained in `polytope`. It is not clear if this is the best algorithm.
    '''
    # TODO: Check if there is a better algorithm.
    for v in potential_subpolytope.vertices():
        if not polytope.contains(v):
            return False
    return True
