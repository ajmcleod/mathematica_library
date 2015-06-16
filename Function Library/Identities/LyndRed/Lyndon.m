(* ::Package:: *)

LyndOrder[0]=0;
LyndOrder[u]=1;
LyndOrder[1-u]=2;
LyndOrder[-1]=3;
LyndOrder[var3]=3;
LyndOrder[1-var3]=3;
LyndOrder[var4]=4;
LyndOrder[1-var4]=4;
LyndOrder[1]=4;
LyndOrder[1/yu]=5;
LyndOrder[1-1/yu]=6;
LyndOrder[1/yv]=7;
LyndOrder[1-1/yv]=8;
LyndOrder[1/(yu*yv)]=9;
LyndOrder[1-1/(yu*yv)]=10;

GredL[{},b_]:=1;
HredL[{},b_]:=1;
GredL[A_,b_]:=GredL[A,b]=Block[{Atemp,vars,FFF}, 
  vars=FFF/@SortBy[Union[A],LyndOrder]; 
  Atemp=(FFF/@A)/. Thread[vars->Array[lyn,Length[vars]]]; 
  If[Length[vars]>1,Expand[Evaluate[Symbol["LyndRed"<>ToString[Length[vars]]<>"Ew"<>ToString[Max[Length[Atemp],5]]]][Atemp]/. Thread[Array[lyn,Length[vars]]->vars]/. FFF[C__]:>C/. QR[B__]:>G[{B},b]],G[A,b]]];
HredL[A_,b_]:=HredL[A,b]=Block[{Atemp,vars,FFF}, 
  vars=FFF/@SortBy[Union[A],LyndOrder]; 
  Atemp=(FFF/@A)/. Thread[vars->Array[lyn,Length[vars]]];
  If[Length[vars]>1,Expand[Evaluate[Symbol["LyndRed"<>ToString[Length[vars]]<>"Ew"<>ToString[Max[Length[Atemp],5]]]][Atemp]/. Thread[Array[lyn,Length[vars]]->vars]/. FFF[C__]:>C/. QR[B__]:>HPL[{B},b]],HPL[A,b]]];

LyndRed2Ew5[word_]:=Module[{},LyndRed2Ew5[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed2Ew5_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed2Ew5 definitions loaded"]];
  LyndRed2Ew5[word]];
LyndRed2Ew6[word_]:=Module[{},LyndRed2Ew6[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed2Ew6_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed2Ew6 definitions loaded"]];
  LyndRed2Ew6[word]]
LyndRed2Ew7[word_]:=Module[{},LyndRed2Ew7[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed2Ew7_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed2Ew7 definitions loaded"]];
  LyndRed2Ew7[word]]
LyndRed2Ew8[word_]:=Module[{},LyndRed2Ew8[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed2Ew8_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed2Ew8 definitions loaded"]];
  LyndRed2Ew8[word]]
LyndRed2Ew9[word_]:=Module[{},LyndRed2Ew9[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed2Ew9_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed2Ew9 definitions loaded"]];
  LyndRed2Ew9[word]]
LyndRed2Ew10[word_]:=Module[{},LyndRed2Ew10[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed2Ew10_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed2Ew10 definitions loaded"]];
  LyndRed2Ew10[word]]

LyndRed3Ew5[word_]:=Module[{},LyndRed3Ew5[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed3Ew5_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed3Ew5 definitions loaded"]];
  LyndRed3Ew5[word]];
LyndRed3Ew6[word_]:=Module[{},LyndRed3Ew6[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed3Ew6_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed3Ew6 definitions loaded"]];
  LyndRed3Ew6[word]]
LyndRed3Ew7[word_]:=Module[{},LyndRed3Ew7[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed3Ew7_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed3Ew7 definitions loaded"]];
  LyndRed3Ew7[word]]
LyndRed3Ew8[word_]:=Module[{},LyndRed3Ew8[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed3Ew8_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed3Ew8 definitions loaded"]];
  LyndRed3Ew8[word]]
LyndRed3Ew9[word_]:=Module[{},LyndRed3Ew9[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed3Ew9_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed3Ew9 definitions loaded"]];
  LyndRed3Ew9[word]]
LyndRed3Ew10[word_]:=Module[{},LyndRed3Ew10[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed3Ew10_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed3Ew10 definitions loaded"]];
  LyndRed3Ew10[word]]

LyndRed4Ew5[word_]:=Module[{},LyndRed4Ew5[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed4Ew5_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed4Ew5 definitions loaded"]];
  LyndRed4Ew5[word]];
LyndRed4Ew6[word_]:=Module[{},LyndRed4Ew6[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed4Ew6_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed4Ew6 definitions loaded"]];
  LyndRed4Ew6[word]]
LyndRed4Ew7[word_]:=Module[{},LyndRed4Ew7[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed4Ew7_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed4Ew7 definitions loaded"]];
  LyndRed4Ew7[word]]
LyndRed4Ew8[word_]:=Module[{},LyndRed4Ew8[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed4Ew8_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed4Ew8 definitions loaded"]];
  LyndRed4Ew8[word]]
LyndRed4Ew9[word_]:=Module[{},LyndRed4Ew9[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed4Ew9_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed4Ew9 definitions loaded"]];
  LyndRed4Ew9[word]]
LyndRed4Ew10[word_]:=Module[{},LyndRed4Ew10[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed4Ew10_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed4Ew10 definitions loaded"]];
  LyndRed4Ew10[word]]

LyndRed5Ew5[word_]:=Module[{},LyndRed5Ew5[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed5Ew5_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed5Ew5 definitions loaded"]];
  LyndRed5Ew5[word]];
LyndRed5Ew6[word_]:=Module[{},LyndRed5Ew6[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed5Ew6_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed5Ew6 definitions loaded"]];
  LyndRed5Ew6[word]]
LyndRed5Ew7[word_]:=Module[{},LyndRed5Ew7[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed5Ew7_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed5Ew7 definitions loaded"]];
  LyndRed5Ew7[word]]
LyndRed5Ew8[word_]:=Module[{},LyndRed5Ew8[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed5Ew8_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed5Ew8 definitions loaded"]];
  LyndRed5Ew8[word]]
LyndRed5Ew9[word_]:=Module[{},LyndRed5Ew9[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed5Ew9_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed5Ew9 definitions loaded"]];
  LyndRed5Ew9[word]]
LyndRed5Ew10[word_]:=Module[{},LyndRed5Ew10[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Local Binaries/LyndRed5Ew10_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["LyndRed5Ew10 definitions loaded"]];
  LyndRed5Ew10[word]]
