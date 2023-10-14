
#Source not specified: All state variables are false!

#Target: All bits are 1.

target A(0) and A(1) and A(2) and A(3) and A(4) and A(5) and A(6) and A(7) and A(8) and A(9)
  and A(10) and A(11) and A(12) and A(13) and A(14) and A(15) and A(16) and A(17) and A(18) and A(19)
  and A(20) and A(21) and A(22) and A(23) and A(24) and A(25) and A(26) and A(27) and A(28) and A(29)
  and A(30) and A(31) and A(32) and A(33) and A(34) and A(35) and A(36) and A(37) and A(38) and A(39)
  and A(40) and A(41) and A(42) and A(43) and A(44) and A(45) and A(46) and A(47) and A(48) and A(49)
  and A(50) and A(51) and A(52) and A(53) and A(54) and A(55) and A(56) and A(57) and A(58) and A(59);

# Every transition turns one bit 1.

transition setbit(i : [0,59])
TRUE
{ A(i); }

# Comment
# With SAT and partially ordered transition sequences this problem
# is trivial, as all transitions are independent. Without the partial
# ordering, the proofs that sequences of length N-1 and shorter
# do not exist become very difficult. However, source-target sequences
# could still be found fast without knowledge the required transition
# sequence length if multiple SAT solvers were run at the same time
# for different lengths.
