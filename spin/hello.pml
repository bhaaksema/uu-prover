byte x ;

active proctype P1() { 
  do /* repeat forever */
  :: x = x+1 ; printf("Hello (%u)!\n", x) ;
  :: break ;
  od ;
  assert x<3 ;
  printf("\nBye!\n") ;
}
