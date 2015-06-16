(* ::Package:: *)

\[LeftAngleBracket] x_, x_ \[RightAngleBracket] := 0; 
\[LeftAngleBracket] x_, 1 - (x_) \[RightAngleBracket] := 0; 
\[LeftAngleBracket] 1 - (x_), x_ \[RightAngleBracket] := 0; 
\[LeftAngleBracket] v, u \[RightAngleBracket] := -\[LeftAngleBracket] u, v \[RightAngleBracket]; 
\[LeftAngleBracket] 1 - v, u \[RightAngleBracket] := -\[LeftAngleBracket] u, 1 - v \[RightAngleBracket];   
\[LeftAngleBracket] 1 - u, v \[RightAngleBracket] := -\[LeftAngleBracket] v, 1 - u \[RightAngleBracket]; 
\[LeftAngleBracket] 1 - v, 1 - u \[RightAngleBracket] := -\[LeftAngleBracket] 1 - u, 1 - v \[RightAngleBracket]; 
\[LeftAngleBracket] u - v, u \[RightAngleBracket] := -\[LeftAngleBracket] u, u - v \[RightAngleBracket]; 
\[LeftAngleBracket] u - v, v \[RightAngleBracket] := -\[LeftAngleBracket] v, u - v \[RightAngleBracket]; 
\[LeftAngleBracket] u - v, 1 - u \[RightAngleBracket] := -\[LeftAngleBracket] 1 - u, u - v \[RightAngleBracket]; 
\[LeftAngleBracket] u - v, 1 - v \[RightAngleBracket] := -\[LeftAngleBracket] 1 - v, u - v \[RightAngleBracket]; 
\[LeftAngleBracket] u, u - v \[RightAngleBracket] := \[LeftAngleBracket] u, v \[RightAngleBracket] + \[LeftAngleBracket] v, u - v \[RightAngleBracket];
\[LeftAngleBracket] 1 - u, 1 - v \[RightAngleBracket] := \[LeftAngleBracket] 1 - u, u - v \[RightAngleBracket] - \[LeftAngleBracket] 1 - v, u - v \[RightAngleBracket];
