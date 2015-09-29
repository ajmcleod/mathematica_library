(* ::Package:: *)

invertArgument[arg_,\[Delta]_]:=func_:>optimizeInvertArgumentReplacement[func,arg,\[Delta]]
optimizeInvertArgumentReplacement[func_,arg_,\[Delta]_]:=Module[{lettersAppearing,letters},
    lettersAppearing=Select[Range[5,Max[transcendentalWeight[func],5]],!FreeQ[func,HPL[aVec_,arg]/;Length[aVec]==#]&];
    If[FreeQ[lettersAppearing,5],If[Or@@Table[!FreeQ[func,HPL[aVec_,arg]/;Length[aVec]==ii],{ii,4}],AppendTo[lettersAppearing,5]]];
    Expand[func/.Join@@Table[Symbol["invertArgument2Ew"<>ToString[ii]<>"HPL"][arg,\[Delta]],{ii,lettersAppearing}]]]

invertArgument2Ew5HPL[arg_,\[Delta]_]:=Module[{},invertArgument2Ew5HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/invertArgument/Local Binaries/invertArgument2Ew5HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 5 invert HPL argument identities loaded"]];
  invertArgument2Ew5HPL[arg,\[Delta]]];
invertArgument2Ew6HPL[arg_,\[Delta]_]:=Module[{},invertArgument2Ew6HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/invertArgument/Local Binaries/invertArgument2Ew6HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 6 invert HPL argument identities loaded"]];
  invertArgument2Ew6HPL[arg,\[Delta]]];
invertArgument2Ew7HPL[arg_,\[Delta]_]:=Module[{},invertArgument2Ew7HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/invertArgument/Local Binaries/invertArgument2Ew7HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 7 invert HPL argument identities loaded"]];
  invertArgument2Ew7HPL[arg,\[Delta]]];
invertArgument2Ew8HPL[arg_,\[Delta]_]:=Module[{},invertArgument2Ew8HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/invertArgument/Local Binaries/invertArgument2Ew8HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 8 invert HPL argument identities loaded"]];
  invertArgument2Ew8HPL[arg,\[Delta]]];
invertArgument2Ew9HPL[arg_,\[Delta]_]:=Module[{},invertArgument2Ew9HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/invertArgument/Local Binaries/invertArgument2Ew9HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 9 invert HPL argument identities loaded"]];
  invertArgument2Ew9HPL[arg,\[Delta]]];
invertArgument2Ew10HPL[arg_,\[Delta]_]:=Module[{},invertArgument2Ew10HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/invertArgument/Local Binaries/invertArgument2Ew10HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 10 invert HPL argument identities loaded"]];
  invertArgument2Ew10HPL[arg,\[Delta]]];

invertArgument3Ew5HPL[arg_,\[Delta]_]:=Module[{},invertArgument3Ew5HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/invertArgument/Local Binaries/invertArgument3Ew5HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 5 invert HPL argument identities loaded"]];
  invertArgument3Ew5HPL[arg,\[Delta]]];
invertArgument3Ew6HPL[arg_,\[Delta]_]:=Module[{},invertArgument3Ew6HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/invertArgument/Local Binaries/invertArgument3Ew6HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 6 invert HPL argument identities loaded"]];
  invertArgument3Ew6HPL[arg,\[Delta]]];
invertArgument3Ew7HPL[arg_,\[Delta]_]:=Module[{},invertArgument3Ew7HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/invertArgument/Local Binaries/invertArgument3Ew7HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 7 invert HPL argument identities loaded"]];
  invertArgument3Ew7HPL[arg,\[Delta]]];
invertArgument3Ew8HPL[arg_,\[Delta]_]:=Module[{},invertArgument3Ew8HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/invertArgument/Local Binaries/invertArgument3Ew8HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 8 invert HPL argument identities loaded"]];
  invertArgument3Ew8HPL[arg,\[Delta]]];
invertArgument3Ew9HPL[arg_,\[Delta]_]:=Module[{},invertArgument3Ew9HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/invertArgument/Local Binaries/invertArgument3Ew9HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 9 invert HPL argument identities loaded"]];
  invertArgument3Ew9HPL[arg,\[Delta]]];
invertArgument3Ew10HPL[arg_,\[Delta]_]:=Module[{},invertArgument3Ew10HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/invertArgument/Local Binaries/invertArgument3Ew10HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 10 invert HPL argument identities loaded"]];
  invertArgument3Ew10HPL[arg,\[Delta]]];
