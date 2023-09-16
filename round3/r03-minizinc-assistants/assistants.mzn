%
% Do NOT modify the following definition lines.
% The values for the constants below will be defined in an external data file.
%
% The number of groups. An integer constant.
int: nofGroups;
% The set {1,..,nofGroups}. We can use "Groups" instead of "1..nofGroups" from now on,
% for examples see the datafile consistency constraints later in this file.
set of int: Groups = 1..nofGroups;
% Group names, just for pretty printing
array[Groups] of string: groupName;
% The minimum amount of assistants required in a group
array[Groups] of int: groupMinCapacity;

% The number of assistants. An integer constant.
int: nofAssistants;
% Again, "Assistants" can be used instead of "1..nofAssistants" from now on
set of int: Assistants = 1..nofAssistants;
% Assistant names, just for pretty printing
array[Assistants] of string: assistantName;
% In at most how many groups is the assistants willing to teach
array[Assistants] of int: assistantMaxGroups;
% assistantGroupOk[a,g] is true iff the assistant "a" can teach in the group "g"
array[Assistants,Groups] of bool: assistantGroupOk;
% The experience level of each assistant
array[Assistants] of int: assistantExperience;
% The cost of each assistant
array[Assistants] of int: assistantCost;

% The total amount of money in use
int: budget;

% The schedule, i.e., how to allocate the assistants to the groups.
% A two-dimensional array of Boolean variables, schedule[a,g] is true if the assistant a
% is teaching in the group g.
% Your constraints should force this array to be such that it fulfills the requirements
% given in the exercise description.
array[Assistants,Groups] of var bool: schedule;

% Check data file consistency
constraint assert(nofGroups >= 1, "There must be at least one group");
constraint assert(forall(g in Groups)(groupMinCapacity[g] >= 1), "Invalid datafile: minimum group capacities must be at least 1");
constraint assert(forall(a in Assistants)(assistantMaxGroups[a] >= 1), "Invalid datafile: each assistant must be willing to teach in at least one group");

% Insert your "constraint" and "solve" statements here
% The experience level of each assistant
% The end time of the last task, i.e., the total time use
var int: expertise;
% Each group has to have some minimal number of assistants in it.
constraint forall(g in Groups)(sum(a in Assistants)(schedule[a,g] == true) >= groupMinCapacity[g]);
% Each assistant must be teaching in at least one group.
constraint forall(a in Assistants)(sum(g in Groups)(schedule[a,g] == true) >= 1);
% Each assistant must be teaching in at least one group.
constraint forall(a in Assistants)(sum(g in Groups)(schedule[a,g] == true) <= assistantMaxGroups[a]);
% As each assistant must also study, they can only teach in some specific groups that they have indicated to you via an online poll.
constraint forall(a in Assistants, g in Groups)(if assistantGroupOk[a,g] == false then schedule[a,g] == false else schedule[a,g] == true \/ schedule[a,g] == false endif);
% The department has allocated a certain maximum amount of money that can be spent in running the tutorial groups of a week.
constraint sum(a in Assistants, g in Groups)(if schedule[a,g] == true then assistantCost[a] else 0 endif) <= budget;
% Max expertise in every group
constraint sum(g in Groups, a in Assistants)(if schedule[a,g] == true then assistantExperience[a] else 0 endif) == expertise;

% Solve max expertise in every group
solve maximize expertise;

% Do NOT modify the following line, it is used in the grading process
output ["Solution:\n"] ++ [(if a == 1 then groupName[g]++": " else "" endif)++ if fix(schedule[a,g]) then " "++assistantName[a] else "" endif ++(if a == nofAssistants then "\n" else "" endif) | g in Groups, a in Assistants];
% If you want to output your own lines, put the "output" statements after this line
% But make sure that they are not of form "Gx: ..." for any integer x
