chan link = [2] of {byte} ;

proctype sender(chan c) { 
  byte x = 0 ;
  do /* repeat forever */
  :: printf("Sending %u\n", x) ; c!x ; x = (x+1)%4 ; 
  od ;
}

proctype receiver(chan c) { 
  byte r ;
  byte trash ;
  bool corrupt = false ;
  do /* repeat forever */
  :: c?r     -> corrupt = false ; printf("Receiving %u\n", r) ; 
  :: c?trash -> corrupt = true  ; printf("CORRUPTED\n") ; (false) ;
  od ;
}

init {
  run sender(link) ;
  run receiver(link) ;
}

ltl second {
  []((sender:x==0) -> <>(receiver:r==0))
}

ltl third {
  []((sender:x == 0) -> (receiver:corrupt == false) U (receiver:corrupt == true || receiver:r == 0))
}
