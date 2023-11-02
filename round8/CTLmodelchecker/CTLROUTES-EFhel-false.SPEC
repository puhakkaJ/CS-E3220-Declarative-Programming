
# One-way flights between locations

type location = { Helsinki, Berlin, Praha, Lisboa, Singapore };

# The initial state includes not only the initial location,
# but also the static facts about possible flights. It is
# typical that some facts do not change, and are stated
# in the initial state description.

source at(Lisboa),
       flight(Lisboa,Berlin),
       flight(Berlin,Lisboa),
       flight(Praha,Singapore),
       flight(Praha,Helsinki);

# No path from Lisboa to Helsinki.

# Is there a path to Helsinki?
ctltarget ctlEF at(Helsinki);
       

# These flights are directed, so there might be no return flight.

transition fly(l1 : location, l2 : location)
at(l1) and flight(l1,l2)
{ not at(l1); at(l2); }
