(* ::Package:: *)

MZV[1]={};
MZV[2]={\[Zeta][2]};
MZV[3]={\[Zeta][3]};
MZV[4]={\[Zeta][2]^2};
MZV[5]={\[Zeta][5],\[Zeta][3]\[Zeta][2]};
MZV[6]={\[Zeta][2]^3,\[Zeta][3]^2};
MZV[7]={\[Zeta][7],\[Zeta][5]\[Zeta][2],\[Zeta][3]\[Zeta][2]^2};
MZV[8]={\[Zeta][2]^4,\[Zeta][5,3],\[Zeta][3]\[Zeta][5],\[Zeta][2]\[Zeta][3]^2};
MZV[9]={\[Zeta][9],\[Zeta][3]^3,\[Zeta][7]\[Zeta][2],\[Zeta][5]\[Zeta][2]^2,\[Zeta][3]\[Zeta][2]^3};
MZV[10]={\[Zeta][2]^5,\[Zeta][7,3],\[Zeta][3]\[Zeta][7],\[Zeta][5]^2,\[Zeta][5,3]\[Zeta][2],\[Zeta][3]\[Zeta][5]\[Zeta][2],\[Zeta][2]^2 \[Zeta][3]^2};

\[Zeta][a__]:=Module[{},\[Zeta][temp__]=.;
  Get[$MathematicaLibrary<>"/Function Library/MZV/Local Binaries/MZV2E_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["MZV identities loaded"]];
  \[Zeta][a]];
\[Zeta][a___,b_?Negative,c___]:=Module[{},\[Zeta][temp1___,temp2_?Negative,temp3___]=.;
  Get[$MathematicaLibrary<>"/Function Library/MZV/Local Binaries/MZV3E_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["Alternating Sum identities loaded"]];
  \[Zeta][a,b,c]];
\[Zeta]n[a__]:=Module[{},\[Zeta]n[temp1__]=.;
  Get[$MathematicaLibrary<>"/Function Library/MZV/Local Binaries/MZVnumerics_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["MZV numerics loaded"]];
  \[Zeta]n[a]];

\[Pi]to\[Zeta]=<|Pi^(10)->93555*\[Zeta][10],Pi^9->9450*Pi*\[Zeta][8],Pi^8->9450*\[Zeta][8],Pi^7->945*Pi*\[Zeta][6],Pi^6->945*\[Zeta][6],Pi^5->90*Pi*\[Zeta][4],Pi^4->90*\[Zeta][4],Pi^3->6*Pi*\[Zeta][2],Pi^2->6\[Zeta][2],\[Delta]^2->1,\[Delta]^3->\[Delta],\[Delta]^4->1,\[Delta]^5->\[Delta],\[Delta]^6->1,\[Delta]^7->\[Delta],\[Delta]^8->1,\[Delta]^9->\[Delta],\[Delta]^10->1|>;
\[Zeta]to\[CapitalZeta]=<|\[Zeta][2]^4 -> 175*\[CapitalZeta][8]/24, \[Zeta][2]^3 -> 35*\[CapitalZeta][6]/8, \[Zeta][2]^2 -> 5*\[CapitalZeta][4]/2, \[Zeta] -> \[CapitalZeta]|>;
pureMZV=Alternatives[\[Zeta][a__],\[Zeta][a__]\[Zeta][b__],\[Zeta][a__]\[Zeta][b__]\[Zeta][c__],\[Zeta][a__]\[Zeta][b__]\[Zeta][c__]\[Zeta][d__],Power[\[Zeta][a__],p1_],\[Zeta][a__]Power[\[Zeta][b__],p1_],Power[\[Zeta][b__],p1_]Power[\[Zeta][c__],p2_],\[Zeta][a__]\[Zeta][b__]Power[\[Zeta][c__],p1_],\[Zeta][a__]Power[\[Zeta][b__],p2_]Power[\[Zeta][c__],p3_]];

(*Identites found in MZV datamine: http://www.nikhef.nl/~form/datamine/mzv/complete/complete.html *)
