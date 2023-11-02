
# One-way flights between locations

type location = { Helsinki, Berlin, Praha, Lisboa, Singapore };

# The initial state includes not only the initial location,
# but also the static facts about possible flights. It is
# typical that some facts do not change, and are stated
# in the initial state description.

source at(Lisboa),
       flight(Lisboa,Berlin),
       flight(Berlin,Praha),
       flight(Praha,Lisboa),
       flight(Praha,Singapore),
       flight(Praha,Helsinki);

# There is a cul-de-sac to Singapore, where you cannot get to Helsinki any more.

# No matter where you have gone, it is always possible to get to Helsinki.
ctltarget ctlAG ctlEF at(Helsinki);

# These flights are directed, so there might be no return flight.

transition fly(l1 : location, l2 : location)
at(l1) and flight(l1,l2)
{ not at(l1); at(l2); }
