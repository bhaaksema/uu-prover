#define N 4
#define FREE  N
#define TRUE  1
#define FALSE 0
#define NEXT(i) (i+1)%N
byte fork[N] ;
bool eating[N] ;

proctype Philosopher(byte i) {
    do
    :: atomic {
        ((fork[i]==FREE) && (fork[NEXT(i)]==FREE)) ;
        fork[i] = i ;
        fork[NEXT(i)] = i 
    } 
        /* prove that here we do indeed have the forks: */
        assert (fork[i]==i) && (fork[NEXT(i)]==i) ;
        eating[i] = TRUE ;
        eating[i] = FALSE ;
        fork[i] = FREE ;
        fork[NEXT(i)] = FREE
    od
}

init {
    byte k = 0 ;
    /* initially, all forks are free */
    do
    :: k<N  -> fork[k] = FREE ; k++
    :: k==N -> break
    od
    k = 0 ;
    /* create the philosophers and run them: */
    atomic {
        do
        :: k<N  -> run Philosopher(k) ; k++
        :: k==N -> break
        od
    }
}

// We translate being deadlock free to the statement:
// Always eventually Phil(i) will hold fork[i] and fork[NEXT(i)]
ltl first {
    [](<>(
        fork[0] == 0 && fork[NEXT(0)] == 0 ||
        fork[1] == 1 && fork[NEXT(1)] == 1 ||
        fork[2] == 2 && fork[NEXT(2)] == 2 ||
        fork[3] == 3 && fork[NEXT(3)] == 3
    ))
}

// When Phil(1) and Phil(3) refrain from eating Phil(0) will eventually eat
// (tested with weak fairness flag 'pan -f' enabled)
ltl second {
    [](
        ([](eating[1] == FALSE && eating[3] == FALSE)) ->
        <>(eating[0] == TRUE)
    )
}
