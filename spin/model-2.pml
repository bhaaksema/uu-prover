#define N 4
#define FREE  N
#define TRUE  1
#define FALSE 0
#define NEXT(i) (i+1)%N
byte fork[N] ;
bool eating[N] ;

proctype Philosopher(byte i) {
    do ::
        /* 
         * we split the large atomic in two atomics for the two forks, to
         * avoid deadlock we play with the order in which the forks are
         * being picked up. if the philosophers number is even it will first
         * pick up fork i, and fork NEXT(i) otherwise.
         */
        if :: (i % 2 == 0) ; atomic { (fork[i]==FREE) ; fork[i] = i } ; fi
        atomic { (fork[NEXT(i)]==FREE) ; fork[NEXT(i)] = i }
        if :: (i % 2 != 0) ; atomic { (fork[i]==FREE) ; fork[i] = i } fi

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
// When Phil(i) holds fork[i] or fork[NEXT(i)] they will eventualy hold both
ltl third {
    [](
        (((fork[0] == 0) -> <>(fork[0] == 0 && fork[NEXT(0)] == 0)) ||
        ((fork[NEXT(0)] == 0) -> <>(fork[0] == 0 && fork[NEXT(0)] == 0))) &&
        (((fork[1] == 1) -> <>(fork[1] == 1 && fork[NEXT(1)] == 1)) ||
        ((fork[NEXT(1)] == 1) -> <>(fork[1] == 1 && fork[NEXT(1)] == 1))) &&
        (((fork[2] == 2) -> <>(fork[2] == 2 && fork[NEXT(2)] == 2)) ||
        ((fork[NEXT(2)] == 2) -> <>(fork[2] == 2 && fork[NEXT(2)] == 2))) &&
        (((fork[3] == 3) -> <>(fork[3] == 3 && fork[NEXT(3)] == 3)) ||
        ((fork[NEXT(3)] == 3) -> <>(fork[3] == 3 && fork[NEXT(3)] == 3)))
    )
}
