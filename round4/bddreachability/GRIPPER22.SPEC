
type room = { rooma, roomb};
type ball = { ball22 , ball21 , ball20 , ball19 , ball18 , ball17 , ball16 , ball15 , ball14, ball13 , ball12 , ball11 , ball10 , ball9 , ball8 , ball7 , ball6 , ball5 , ball4, ball3 , ball2 , ball1 };
type gripper = { left, right };

transition move( from : room, to : room )
atrobot(from)
{ atrobot(to);
  not atrobot(from); }

transition pick ( obj : ball, room : room, gripper : gripper)
at(obj,room) and atrobot(room) and free(gripper)
{ carry(obj,gripper);
  not at(obj,room);
  not free(gripper); }

transition drop ( obj : ball, room : room, gripper : gripper)
carry(obj,gripper) and atrobot(room)
{ at(obj,room);
  free(gripper);
  not carry(obj,gripper); }

source atrobot(rooma),
          free(left),
          free(right),
          at(ball22,rooma),
          at(ball21,rooma),
          at(ball20,rooma),
          at(ball19,rooma),
          at(ball18,rooma),
          at(ball17,rooma),
          at(ball16,rooma),
          at(ball15,rooma),
          at(ball14,rooma),
          at(ball13,rooma),
          at(ball12,rooma),
          at(ball11,rooma),
          at(ball10,rooma),
          at(ball9,rooma),
          at(ball8,rooma),
          at(ball7,rooma),
          at(ball6,rooma),
          at(ball5,rooma),
          at(ball4,rooma),
          at(ball3,rooma),
          at(ball2,rooma),
          at(ball1,rooma);

target at(ball22,roomb) and at(ball21,roomb) and at(ball20,roomb) and at(ball19,roomb) and at(ball18,roomb) and at(ball17,roomb) and at(ball16,roomb) and at(ball15,roomb) and at(ball14,roomb) and at(ball13,roomb) and at(ball12,roomb) and at(ball11,roomb) and at(ball10,roomb) and at(ball9,roomb) and at(ball8,roomb) and at(ball7,roomb) and at(ball6,roomb) and at(ball5,roomb) and at(ball4,roomb) and at(ball3,roomb) and at(ball2,roomb) and at(ball1,roomb);
