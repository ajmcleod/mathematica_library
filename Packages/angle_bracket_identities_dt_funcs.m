(* ::Package:: *)

\[LeftAngleBracket] x_, x_ \[RightAngleBracket] := 0; 
\[LeftAngleBracket] x_, 1 - (x_) \[RightAngleBracket] := 0; 
\[LeftAngleBracket] 1 - (x_), x_ \[RightAngleBracket] := 0; 
\[LeftAngleBracket] w, u \[RightAngleBracket] := -\[LeftAngleBracket] u, w \[RightAngleBracket]; 
\[LeftAngleBracket] 1 - w, u \[RightAngleBracket] := -\[LeftAngleBracket] u, 1 - w \[RightAngleBracket];   
\[LeftAngleBracket] 1 - u, w \[RightAngleBracket] := -\[LeftAngleBracket] w, 1 - u \[RightAngleBracket]; 
\[LeftAngleBracket] 1 - w, 1 - u \[RightAngleBracket] := -\[LeftAngleBracket] 1 - u, 1 - w \[RightAngleBracket]; 
\[LeftAngleBracket] 1 - u*w, u \[RightAngleBracket] := -\[LeftAngleBracket] u, 1 - u*w \[RightAngleBracket]; 
\[LeftAngleBracket] 1 - u*w, w \[RightAngleBracket] := -\[LeftAngleBracket] w, 1 - u*w \[RightAngleBracket]; 
\[LeftAngleBracket] 1 - u*w, 1 - u \[RightAngleBracket] := -\[LeftAngleBracket] 1 - u, 1 - u*w \[RightAngleBracket]; 
\[LeftAngleBracket] 1 - u*w, 1 - w \[RightAngleBracket] := -\[LeftAngleBracket] 1 - w, 1 - u*w \[RightAngleBracket]; 
\[LeftAngleBracket] u, 1 - u*w \[RightAngleBracket] := - \[LeftAngleBracket] w, 1 - u*w \[RightAngleBracket];
\[LeftAngleBracket] 1 - u, 1 - u*w \[RightAngleBracket] := \[LeftAngleBracket] 1 - u, 1 - w \[RightAngleBracket] + \[LeftAngleBracket] u, 1 - u*w \[RightAngleBracket] + \[LeftAngleBracket] 1 - w, 1 - u*w \[RightAngleBracket];
