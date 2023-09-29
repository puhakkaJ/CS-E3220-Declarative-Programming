
type room = { rooma, roomb};
type ball = { ball6 , ball5 , ball4, ball3 , ball2 , ball1 };
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
          at(ball6,rooma),
          at(ball5,rooma),
          at(ball4,rooma),
          at(ball3,rooma),
          at(ball2,rooma),
          at(ball1,rooma);

target at(ball6,roomb) and at(ball5,roomb) and at(ball4,roomb) and at(ball3,roomb) and at(ball2,roomb) and at(ball1,roomb);
