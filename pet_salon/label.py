r'''
This file provides a class `Relabeler` for keeping track of integer labels, possibly for relabeling an object.
'''
# ********************************************************************
#  This file is part of pet-salon.
#
#        Copyright (C) 2024 W. Patrick Hooper
#
#  sage-flatsurf is free software: you can redistribute it and/or modify
#  it under the terms of the GNU General Public License as published by
#  the Free Software Foundation, either version 2 of the License, or
#  (at your option) any later version.
#
#  sage-flatsurf is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with sage-flatsurf. If not, see <https://www.gnu.org/licenses/>.
# ********************************************************************

class Relabeler():
    r'''A simple class to replace a collection of labels with integers.

    EXAMPLES::

        sage: from pet_salon.label import Relabeler
        sage: r = Relabeler()
        sage: r.new_label(sqrt(2))
        0
        sage: r.new_label(x)
        1
        sage: r.old_label(0)
        sqrt(2)
        sage: r.old_label(1)
        x
    '''
    def __init__(self):
        self._old_to_new = {}
        self._new_to_old = []

    def new_label(self, old_label):
        try:
            return self._old_to_new[old_label]
        except KeyError:
            n = len(self._new_to_old)
            self._new_to_old.append(old_label)
            self._old_to_new[old_label] = n
            return n

    def old_label(self, new_label):
        return self._new_to_old[new_label]
