# FT-FFTW
Fault tolerant version of FFTW

# install && execute
1. cd src/ft-fftw-3.3.5-oop
2. ./configure --enable-mpi --prefix=myDirectory
3. make -j 4 && make install
4. cd ..
5. mpicc mpi_outofplace.c -o ftfftw.o -L/myDirectory/lib -lfftw3_mpi -lfftw3 -lm -I/myDirectory/include
6. mpirun -n 256 ftfftw.o > output.txt

# fault injection
Faults can be injected at runtime or in source code. However, if two faults are injected in one decomposed FFT, they are not guaranteed to be detected or corrected.
