(* ::Package:: *)

toSingularArgP[arg_,\[Delta]_]:=func_:>optimizeToSingularArgPReplacement[func,arg,\[Delta]]
optimizeToSingularArgPReplacement[func_,arg_,\[Delta]_]:=Module[{lettersAppearing,letters},
    lettersAppearing=Select[Range[5,Max[transcendentalWeight[func],5]],!FreeQ[func,HPL[aVec_,arg]/;Length[aVec]==#]&];
    If[FreeQ[lettersAppearing,5],If[Or@@Table[!FreeQ[func,HPL[aVec_,arg]/;Length[aVec]==ii],{ii,4}],AppendTo[lettersAppearing,5]]];
    Expand[func/.Join@@Table[Symbol["toSingularArgP2Ew"<>ToString[ii]<>"HPL"][arg,\[Delta]],{ii,lettersAppearing}]]/.HPL[a_,b_]:>HPL[a,Factor[b]]]

toSingularArgP2Ew5HPL[arg_,\[Delta]_]:=Module[{},toSingularArgP2Ew5HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/toSingularArgP/Local Binaries/toSingularArgP2Ew5HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 5 toSingularArgP HPL argument identities loaded"]];
  toSingularArgP2Ew5HPL[arg,\[Delta]]];
toSingularArgP2Ew6HPL[arg_,\[Delta]_]:=Module[{},toSingularArgP2Ew6HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/toSingularArgP/Local Binaries/toSingularArgP2Ew6HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 6 toSingularArgP HPL argument identities loaded"]];
  toSingularArgP2Ew6HPL[arg,\[Delta]]];
toSingularArgP2Ew7HPL[arg_,\[Delta]_]:=Module[{},toSingularArgP2Ew7HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/toSingularArgP/Local Binaries/toSingularArgP2Ew7HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 7 toSingularArgP HPL argument identities loaded"]];
  toSingularArgP2Ew7HPL[arg,\[Delta]]];
toSingularArgP2Ew8HPL[arg_,\[Delta]_]:=Module[{},toSingularArgP2Ew8HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/toSingularArgP/Local Binaries/toSingularArgP2Ew8HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 8 toSingularArgP HPL argument identities loaded"]];
  toSingularArgP2Ew8HPL[arg,\[Delta]]];
toSingularArgP2Ew9HPL[arg_,\[Delta]_]:=Module[{},toSingularArgP2Ew9HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/toSingularArgP/Local Binaries/toSingularArgP2Ew9HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 9 toSingularArgP HPL argument identities loaded"]];
  toSingularArgP2Ew9HPL[arg,\[Delta]]];
toSingularArgP2Ew10HPL[arg_,\[Delta]_]:=Module[{},toSingularArgP2Ew10HPL[temp1_,temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Identities/toSingularArgP/Local Binaries/toSingularArgP2Ew10HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 10 toSingularArgP HPL argument identities loaded"]];
  toSingularArgP2Ew10HPL[arg,\[Delta]]];
