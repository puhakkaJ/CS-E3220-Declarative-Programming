
# Flights between locations

type location = { Helsinki, Berlin, Praha, Lisboa, Singapore, Vancouver };

# The initial state includes not only the initial location,
# but also the static facts about possible flights. It is
# typical that some facts do not change, and are stated
# in the initial state description.

source at(Lisboa),
       flight(Helsinki,Berlin),
       flight(Berlin,Praha),
       flight(Praha,Lisboa);

target at(Helsinki);

# Our transition uses the flights in both ways, so
# what we have specified above with the 'flight'
# predicate is an undirected graph.

transition fly(l1 : location, l2 : location)
at(l1) and (flight(l1,l2) or flight(l2,l1))
{ not at(l1); at(l2); }
