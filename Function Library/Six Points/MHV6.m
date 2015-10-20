(* ::Package:: *)

Y[a_,b_,c_] := Y[a,b,c] = HPL[{0,1},1-a] + HPL[{0,1},1-b] + HPL[{0,1},1-c] + (HPL[{1},1-a]^2 + HPL[{1},1-b]^2 + HPL[{1},1-c]^2)/2;
Subscript[\[Gamma],K] = 4*a - 4*\[Zeta][2]*a^2 + 22*\[Zeta][4]*a^3 - 4*((219/8)*\[Zeta][6]+\[Zeta][3]^2)*a^4 + ((14192*\[Zeta][2]^4)/175 + 8*\[Zeta][2]*\[Zeta][3]^2 + 40*\[Zeta][3]*\[Zeta][5])*a^5 + weight6terms*a^6;

R6[0] = 0;
R6[1] = 0;
R6[2] := Module[{},R6[2]=.;
  Get[$MathematicaLibrary<>"/Function Library/Six Points/Local Binaries/R62_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["R6[2] loaded"]];
  R6[2]];
R6[3] := Module[{},R6[3]=.;
  Get[$MathematicaLibrary<>"/Function Library/Six Points/Local Binaries/R63_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["R6[3] loaded"]];
  R6[3]];
R6[4] := Module[{},R6[4]=.;
  Get[$MathematicaLibrary<>"/Function Library/Six Points/Local Binaries/R64_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["R6[4] loaded"]];
  R6[4]];

EMHV6[0] = 1;
EMHV6[1] := Module[{},EMHV6[1]=.;
  Get[$MathematicaLibrary<>"/Function Library/Six Points/Local Binaries/EMHV61_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["EMHV[1] loaded"]];
  EMHV6[1]];
EMHV6[2] := Module[{},EMHV6[2]=.;
  Get[$MathematicaLibrary<>"/Function Library/Six Points/Local Binaries/EMHV62_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["EMHV[2] loaded"]];
  EMHV6[2]];
EMHV6[3] := Module[{},EMHV6[3]=.;
  Get[$MathematicaLibrary<>"/Function Library/Six Points/Local Binaries/EMHV63_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["EMHV[3] loaded"]];
  EMHV6[3]];
EMHV6[4] := Module[{},EMHV6[4]=.;
  Get[$MathematicaLibrary<>"/Function Library/Six Points/Local Binaries/EMHV64_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["EMHV[4] loaded"]];
  EMHV6[4]];

