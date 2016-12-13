/*
 * Copyright (c) 2003, 2007-14 Matteo Frigo
 * Copyright (c) 2003, 2007-14 Massachusetts Institute of Technology
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301  USA
 *
 */

#include "api.h"
#include <stdbool.h>
int myRadix;
bool firstFFT;
bool secondFFT;
bool FFTstart;
X(plan) X(plan_dft)(int rank, const int *n,
		    C *in, C *out, int sign, unsigned flags)
{
	myRadix = 0;
	firstFFT = false;
	secondFFT = false;
	FFTstart = false;	
     return X(plan_many_dft)(rank, n, 1,
			     in, 0, 1, 1, 
			     out, 0, 1, 1, 
			     sign, flags);
}
