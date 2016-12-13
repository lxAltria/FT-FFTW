#include <fftw3-mpi.h>
#include <time.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
int main(int argc, char **argv)
{
	double elapsed_time1;
	double elapsed_time2;

    //const long long N0 = 1073741824;
    const long long N0 = 2147483648;
    //const long long N0 = 4294967296;
    //const long long N0 = 8589934592; 
    //const long long N0 = 17179869184;

    fftw_plan plan;
    fftw_complex *data, *data2;
    ptrdiff_t alloc_local, local_ni, local_i_start;
	ptrdiff_t local_no, local_o_start;
	ptrdiff_t i;
	int id;

    MPI_Init(&argc, &argv);
    MPI_Comm_rank(MPI_COMM_WORLD, &id);

	fftw_mpi_init();
    alloc_local = fftw_mpi_local_size_1d(N0, MPI_COMM_WORLD, FFTW_FORWARD, FFTW_ESTIMATE, &local_ni, &local_i_start, &local_no, &local_o_start);
    data = fftw_alloc_complex(alloc_local);
    data2 = fftw_alloc_complex(alloc_local);

	elapsed_time1 = -MPI_Wtime();
    plan = fftw_mpi_plan_dft_1d(N0, data, data2, MPI_COMM_WORLD, FFTW_FORWARD, FFTW_ESTIMATE);
	elapsed_time1 += MPI_Wtime();

    srand(time(NULL));
    for (i=0; i<local_ni; i++)
    {
        data[i][0] = 2.0 * ( (float)rand()/RAND_MAX ) - 1.0;
        data[i][1] = 2.0 * ( (float)rand()/RAND_MAX ) - 1.0;
    }

	elapsed_time2 = -MPI_Wtime();
	fftw_execute(plan);
	elapsed_time2 += MPI_Wtime();

	if(!id) 
	{
		printf("Elapsed time1: %f\nElapsed time2: %f\n", elapsed_time1, elapsed_time2);
	}
	fftw_destroy_plan(plan);

    MPI_Finalize();
}
