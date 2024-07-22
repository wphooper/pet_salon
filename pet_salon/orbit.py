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

from enum import Enum

class StopCriterion(Enum):
    NEVER = 0
    PERIODIC = 1

class Orbit:

    def __init__(self, pam, point, stop_criterion=StopCriterion.PERIODIC):

        assert pam.domain() == pam.codomain(), 'Domain and codomain do not match.'
        self._pam = pam

        # We store off the component maps:
        self._p = pam.partition()
        self._pi = ~self._p
        self._ah = pam.affine_homeomorphism()
        self._i = pam.immersion()

        self._point = pam.domain().point_set()(point)

        # We start the orbit:
        self._orbit = [pam.partition()(point)]

        self._stopped = False
        self._stop_criterion = StopCriterion(stop_criterion)

    def stopped(self):
        return self._stopped

    def _stop(self, next_point):
        match self._stop_criterion:
            case StopCriterion.NEVER:
                return False
            case StopCriterion.PERIODIC:
                return next_point == self._orbit[0]

    def iterate(self, n=1):
        r'''
        Iterate the orbit forward n more times.

        Will return `True` if the stop criterion has been triggered, and `False` otherwise.
        '''
        assert not self.stopped(), 'The orbit has stopped!'
        for i in range(n):
            next_point = self._p(self._i(self._ah(self._orbit[-1])))
            if self._stop(next_point):
                self._stopped=True
                return True
            else:
                self._orbit.append(next_point)
        return False

    def is_done(self):
        return self._stopped

    def __len__(self):
        return len(self._orbit)

    def orbit(self, position_only=False, partitioned=False):
        r'''
        Return a generator that should quickly give the orbit.

        If `position_only` is `True` then we just give the position vectors. This is useful for plotting.

        If `partitioned` is `True`, then we will return the image of the orbit under the partition
        function of the PAM.
        '''
        if position_only:
            for partitioned_point in self._orbit:
                yield partitioned_point.position()
        elif partitioned:
            for partitioned_point in self._orbit:
                yield partitioned_point
        else:
            for partitioned_point in self._orbit:
                yield self._pi(partitioned_point)



    def point(self, i=0, position_only=False, partitioned=False):
        r'''
        Return the i-th point in the orbit, $f^i(p)$ where $p$ was the point provided at construction.

        If `position_only` is `True` then we just give the position vector.

        If `partitioned` is `True`, then we will return the image of $f^i(p)$. This has a bit more
        information in it.
        '''
        if position_only:
            return self._orbit[i].position()
        elif partitioned:
            return self._orbit[i]
        else:
            return self._pi(self._orbit[i])
