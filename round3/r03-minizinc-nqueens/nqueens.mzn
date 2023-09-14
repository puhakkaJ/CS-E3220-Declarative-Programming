% Use this editor as a MiniZinc scratch book
% The dimension of the board
% Will be given by the user or read from a data file
% Do NOT modify
int: n;

% The positions of the queens
% The queen in the column col is in the row queens[col]
% This encoding automatically ensures that no column contains two queens
% Do NOT modify
array [1..n] of var 1..n: queens;

% Include the alldifferent constraint so that you can use it
include "alldifferent.mzn";

% In the following constraints, force the following:
% - No two queens can appear in the same row
% - No two queens can appear in the same diagonal
% This can be done with three alldifferent constrains.
% INSERT YOUR CONSTRAINTS HERE

% The values in each row should be distinct
constraint alldifferent (queens);
% The values in each diagonal direction should be distinct
constraint alldifferent([queens[i] + i| i in 1..n]); % upwards
constraint alldifferent([queens[i] - i| i in 1..n]); % downwards


% Search for solutions; do NOT modify.
solve satisfy;

% Output the solution; do NOT modify.
output ["q = \(queens)\n"];
output [if fix(queens[col]) == row then "Q" else "-" endif ++ if col == n then "\n" else "" endif | row,col in 1..n];
