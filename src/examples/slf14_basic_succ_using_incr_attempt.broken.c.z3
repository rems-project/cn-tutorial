return code: 1
[1/2]: incr -- pass
[2/2]: succ_using_incr_attempt -- fail
./src/examples/slf14_basic_succ_using_incr_attempt.broken.c:12:3: error: Left-over unused resource 'Owned<unsigned int>(call_refUnsignedInt0.return)(call_incr0.n2)'
  return *p;
  ^~~~~~~~~~ 
State file: file:///tmp/state__slf14_basic_succ_using_incr_attempt.broken.c__succ_using_incr_attempt.html
