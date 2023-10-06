
# A simple program that is simultaneously run in multiple threads.
# If thread can transfer money from a joint account to their
# personal accounts. The timing in which the transfers are attempted
# makes it possible for all threads to simultaneously confirm that
# money is available in the joint account, and then move the money
# at the same time to each of the personal accounts in full,
# multiplying the amount of money in the system.

#
# p1
#   if jointaccount == 1:
# p2
#     jointaccount = 0
# p3
#     personalaccount[THREAD] = 1
# p4

# In the beginning, all threads are about to start from p1,
# and there is money only in the jointaccount.
source p0(0), p0(1), p0(2), jointaccount;

# In the end, all threads have executed all code.
target personalaccount(2) and not personalaccount(0) and not personalaccount(1);

# There are threads 0,1,2.
type THREAD = [0,2];

transition p0p1(t : THREAD)
p0(t) and not CSoccupied
{
    p1(t); CSoccupied;
}

transition p1p2(t : THREAD)
p1(t) and jointaccount
{
    not p1(t); p2(t);
}

transition p1p4(t : THREAD)
p1(t) and not jointaccount
{
    not p1(t); p3b(t);
}

transition p2p3(t : THREAD)
p2(t)
{
    not p2(t); p3(t);
    not jointaccount;
}

transition p3p3b(t : THREAD)
p3(t)
{
    not p3(t); p3b(t);
    personalaccount(t);
}

transition p3bp4(t : THREAD)
p3b(t)
{
    not p3b(t); p4(t);
    not CSoccupied;
}

   

