(* ::Package:: *)

meToLance=func_:>optimizeMeToLanceReplacement[func]/;(Head[func]=!=List)\[And](func=!=List)
optimizeMeToLanceReplacement[func_]:=Module[{functionWeight=transcendentalWeight[func],evenWeightsAppearing={},oddWeightsAppearing={},SPSweightsAppearing={}},
    If[!FreeQ[func,Alternatives[H3,H4,H5]],AppendTo[evenWeightsAppearing,5];AppendTo[oddWeightsAppearing,5]];
    If[!FreeQ[func,Alternatives[SP2,SP3,SP4,SP5]],AppendTo[SPSweightsAppearing,5]];
    If[functionWeight>5,
       If[!FreeQ[func,H6],AppendTo[evenWeightsAppearing,6];AppendTo[oddWeightsAppearing,6]];
       If[!FreeQ[func,SP6],AppendTo[SPSweightsAppearing,6]];
       If[functionWeight>6,
          If[!FreeQ[func,E7],AppendTo[evenWeightsAppearing,7]];
          If[!FreeQ[func,O7],AppendTo[oddWeightsAppearing,7]];
          If[!FreeQ[func,SP7],AppendTo[SPSweightsAppearing,7]];
          If[functionWeight>7,
             If[!FreeQ[func,E8],AppendTo[evenWeightsAppearing,8]];
             If[!FreeQ[func,O8],AppendTo[oddWeightsAppearing,8]]]]];
    If[debug,Print["odd functions of weight "<>ToString[oddWeightsAppearing]<>" and even functions of weight "<>ToString[evenWeightsAppearing]<>" and SPS functions of weight "<>ToString[SPSweightsAppearing]<>" translated from my notation to Lance's"]];
    Expand[func/.Join@@Table[meToLanceOddWeight[ii],{ii,oddWeightsAppearing}]/.Join@@Table[meToLanceEvenWeight[ii],{ii,evenWeightsAppearing}]/.Join@@Table[meToLanceSPSweight[ii],{ii,SPSweightsAppearing}]]]
       
LanceToMe=func_:>optimizeLanceToMeReplacement[func]/;(Head[func]=!=List)\[And](func=!=List)
optimizeLanceToMeReplacement[func_]:=Module[{functionWeight=transcendentalWeight[func],evenWeightsAppearing={},oddWeightsAppearing={},SPSweightsAppearing={}},
    If[!FreeQ[func,Alternatives[Superscript[\[CapitalOmega], "(2)"][_,_,_], Subscript[Q, "ep"][_,_,_], Subscript[M, 1][_,_,_], N, O]],AppendTo[evenWeightsAppearing,5]];
    If[!FreeQ[func,Alternatives[Subscript[OverTilde[\[CapitalPhi]], 6], Subscript[F, 1][_,_,_], Subscript[K, 1][_,_,_], G, Subscript[H, 1][_,_,_], Subscript[J, 1][_,_,_]]],AppendTo[oddWeightsAppearing,5]];
    If[!FreeQ[func,Alternatives@@Join[{SPw2f1[_,_]},{SPw3f1[_,_],SPw3f2[_,_]},Table[Symbol["SPw4f"<>ToString[ii]][_,_],{ii,7}],Table[Symbol["SPw5f"<>ToString[ii]][_,_],{ii,20}]]],AppendTo[SPSweightsAppearing,5]];
    If[functionWeight>5,
       If[!FreeQ[func,Alternatives@@Table[Symbol["B"<>ToString[ii]][_,_,_],{ii,11}]],AppendTo[evenWeightsAppearing,6]];
       If[!FreeQ[func,Alternatives@@Table[Symbol["A"<>ToString[ii]][_,_,_],{ii,11}]],AppendTo[oddWeightsAppearing,6]];
       If[!FreeQ[func,Alternatives@@Table[Symbol["SPw6f"<>ToString[ii]][_,_],{ii,54}]],AppendTo[SPSweightsAppearing,6]];
       If[functionWeight>6,
          If[!FreeQ[func,Alternatives@@Table[Symbol["D"<>ToString[ii]][_,_,_],{ii,36}]],AppendTo[evenWeightsAppearing,7]];
          If[!FreeQ[func,Alternatives@@Table[Symbol["C"<>ToString[ii]][_,_,_],{ii,28}]],AppendTo[oddWeightsAppearing,7]];
          If[!FreeQ[func,Alternatives@@Table[Symbol["SPw7f"<>ToString[ii]][_,_],{ii,150}]],AppendTo[SPSweightsAppearing,7]];
          If[functionWeight>7,
             If[!FreeQ[func,Alternatives@@Table[Symbol["T"<>ToString[ii]][_,_,_],{ii,102}]],AppendTo[evenWeightsAppearing,8]];
             If[!FreeQ[func,Alternatives@@Table[Symbol["S"<>ToString[ii]][_,_,_],{ii,86}]],AppendTo[oddWeightsAppearing,8]]]]];
    If[debug,Print["odd functions of weight "<>ToString[oddWeightsAppearing]<>" and even functions of weight "<>ToString[evenWeightsAppearing]<>" and SPS functions of weight "<>ToString[SPSweightsAppearing]<>" translated from Lance's notation to mine"]];
    Expand[func/.Join@@Table[LanceToMeOddWeight[ii],{ii,oddWeightsAppearing}]/.Join@@Table[LanceToMeEvenWeight[ii],{ii,evenWeightsAppearing}]/.Join@@Table[LanceToMeSPSweight[ii],{ii,SPSweightsAppearing}]]];

convertMeToLance=func_:>optimizeConvertMeToLanceReplacement[func]/;(Head[func]=!=List)\[And](func=!=List)
optimizeConvertMeToLanceReplacement[func_]:=Module[{functionWeight=transcendentalWeight[func],HPLvars=DeleteDuplicates[Flatten[Reap[func/.HPL[aVec_,arg_]:>(Sow[{arg,Max[Length[aVec],5]}];0)][[2]],1]],flipArgs,conversion=<||>},
    flipArgs=DeleteCases[DeleteDuplicates[Table[First[argsAppearing],{argsAppearing,HPLvars}]],1-_];
    If[!FreeQ[func,Log],AppendTo[conversion,<|Log->ln|>]];
    If[!FreeQ[func,PolyLog],AppendTo[conversion,<|PolyLog->polylog|>]];
    If[!FreeQ[func,\[Zeta]],AppendTo[conversion,convertMeToLanceTerms[\[Zeta]]]];
    If[!FreeQ[func,Alternatives[Subscript[OverTilde[\[CapitalPhi]],6], Superscript[\[CapitalOmega],"(2)"][_,_,_], Subscript[F,1][_,_,_], Subscript[H, 1][_,_,_], Subscript[J, 1][_,_,_], N, O, Subscript[M, 1][_,_,_], Subscript[Q, "ep"][_,_,_], G, Subscript[K, 1][_,_,_]]],AppendTo[conversion,convertMeToLanceTerms[irreducibles]]];
    Do[AppendTo[conversion,convertMeToLanceTerms[HPLs,args[[1]],args[[2]]]],{args,HPLvars/.{1-arg_,weight_}:>{arg,weight}}];
    If[Length[flipArgs]>0,
       func/.flipArgument[flipArgs]/.conversion,
       func/.conversion]]
       
meToLanceOddWeight[weight_]:=Module[{},meToLanceOddWeight[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/meToLanceOdd_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["odd conversions from me to Lance loaded"]];
  meToLanceOddWeight[weight]];
meToLanceEvenWeight[weight_]:=Module[{},meToLanceEvenWeight[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/meToLanceEven_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["even conversions from me to Lance loaded"]];
  meToLanceEvenWeight[weight]];
meToLanceSPSweight[weight_]:=Module[{},meToLanceSPSweight[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/meToLanceSPS_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["SPS conversions from me to Lance loaded"]];
  meToLanceSPSweight[weight]];
LanceToMeOddWeight[weight_]:=Module[{},LanceToMeOddWeight[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/LanceToMeOdd_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["odd conversions from Lance to me loaded"]];
  LanceToMeOddWeight[weight]];
LanceToMeEvenWeight[weight_]:=Module[{},LanceToMeEvenWeight[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/LanceToMeEven_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["even conversions from Lance to me loaded"]];
  LanceToMeEvenWeight[weight]];
LanceToMeSPSweight[weight_]:=Module[{},LanceToMeSPSweight[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/LanceToMeSPS_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["SPS conversions from Lance to me loaded"]];
  LanceToMeSPSweight[weight]];
convertMeToLanceTerms[arg__]:=Module[{},convertMeToLanceTerms[temp__]=.;
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/convertMeToLance_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["notation conversions from me to Lance loaded"]];
  convertMeToLanceTerms[arg]];

Get["symmetriesLowWeight.dat"];
Get["symmetriesA.dat"];
Get["symmetriesB.dat"];
Get["symmetriesC.dat"];
Get["symmetriesD.dat"];
Get["symmetriesSPS.dat"];

convertLanceToMe={z2->\[Zeta][2], z3->\[Zeta][3], z4->\[Zeta][4], z5->\[Zeta][5], z6->\[Zeta][6], z7->\[Zeta][7], z8->\[Zeta][8], Zeta53->\[Zeta][5,3], ln[x_]:>Log[x], polylog[x_,y_]:>PolyLog[x,y], H1m[x_] :> HPL[{1}, 1 - x], H2m[x_] :> HPL[{0, 1}, 1 - x], H3m[x_] :> HPL[{0, 0, 1}, 1 - x], H21m[x_] :> HPL[{0, 1, 1}, 1 - x], H4m[x_] :> HPL[{0, 0, 0, 1}, 1 - x], H31m[x_] :> HPL[{0, 0, 1, 1}, 1 - x], H211m[x_] :> HPL[{0, 1, 1, 1}, 1 - x], H5m[x_] :> HPL[{0, 0, 0, 0, 1}, 1 - x], H41m[x_] :> HPL[{0, 0, 0, 1, 1}, 1 - x], H32m[x_] :> HPL[{0, 0, 1, 0, 1}, 1 - x], H311m[x_] :> HPL[{0, 0, 1, 1, 1}, 1 - x], H221m[x_] :> HPL[{0, 1, 0, 1, 1}, 1 - x], H2111m[x_] :> HPL[{0, 1, 1, 1, 1}, 1 - x], H6m[x_] :> HPL[{0, 0, 0, 0, 0, 1}, 1 - x], H51m[x_] :> HPL[{0, 0, 0, 0, 1, 1}, 1 - x], H42m[x_] :> HPL[{0, 0, 0, 1, 0, 1}, 1 - x], H411m[x_] :> HPL[{0, 0, 0, 1, 1, 1}, 1 - x], H321m[x_] :> HPL[{0, 0, 1, 0, 1, 1}, 1 - x], H312m[x_] :> HPL[{0, 0, 1, 1, 0, 1}, 1 - x], H3111m[x_] :> HPL[{0, 0, 1, 1, 1, 1}, 1 - x], H2211m[x_] :> HPL[{0, 1, 0, 1, 1, 1}, 1 - x], H21111m[x_] :> HPL[{0, 1, 1, 1, 1, 1}, 1 - x], H7m[x_] :> HPL[{0, 0, 0, 0, 0, 0, 1}, 1 - x], H61m[x_] :> HPL[{0, 0, 0, 0, 0, 1, 1}, 1 - x], H52m[x_] :> HPL[{0, 0, 0, 0, 1, 0, 1}, 1 - x], H511m[x_] :> HPL[{0, 0, 0, 0, 1, 1, 1}, 1 - x], H43m[x_] :> HPL[{0, 0, 0, 1, 0, 0, 1}, 1 - x], H421m[x_] :> HPL[{0, 0, 0, 1, 0, 1, 1}, 1 - x], H412m[x_] :> HPL[{0, 0, 0, 1, 1, 0, 1}, 1 - x], H4111m[x_] :> HPL[{0, 0, 0, 1, 1, 1, 1}, 1 - x], H331m[x_] :> HPL[{0, 0, 1, 0, 0, 1, 1}, 1 - x], H322m[x_] :> HPL[{0, 0, 1, 0, 1, 0, 1}, 1 - x], H3211m[x_] :> HPL[{0, 0, 1, 0, 1, 1, 1}, 1 - x], H3121m[x_] :> HPL[{0, 0, 1, 1, 0, 1, 1}, 1 - x], H3112m[x_] :> HPL[{0, 0, 1, 1, 1, 0, 1}, 1 - x], H31111m[x_] :> HPL[{0, 0, 1, 1, 1, 1, 1}, 1 - x], H2221m[x_] :> HPL[{0, 1, 0, 1, 0, 1, 1}, 1 - x], H22111m[x_] :> HPL[{0, 1, 0, 1, 1, 1, 1}, 1 - x], H21211m[x_] :> HPL[{0, 1, 1, 0, 1, 1, 1}, 1 - x], H211111m[x_] :> HPL[{0, 1, 1, 1, 1, 1, 1}, 1 - x], H8m[x_] :> HPL[{0, 0, 0, 0, 0, 0, 0, 1}, 1 - x], H71m[x_] :> HPL[{0, 0, 0, 0, 0, 0, 1, 1}, 1 - x], H62m[x_] :> HPL[{0, 0, 0, 0, 0, 1, 0, 1}, 1 - x], H611m[x_] :> HPL[{0, 0, 0, 0, 0, 1, 1, 1}, 1 - x], H53m[x_] :> HPL[{0, 0, 0, 0, 1, 0, 0, 1}, 1 - x], H521m[x_] :> HPL[{0, 0, 0, 0, 1, 0, 1, 1}, 1 - x], H512m[x_] :> HPL[{0, 0, 0, 0, 1, 1, 0, 1}, 1 - x], H5111m[x_] :> HPL[{0, 0, 0, 0, 1, 1, 1, 1}, 1 - x], H431m[x_] :> HPL[{0, 0, 0, 1, 0, 0, 1, 1}, 1 - x], H422m[x_] :> HPL[{0, 0, 0, 1, 0, 1, 0, 1}, 1 - x], H4211m[x_] :> HPL[{0, 0, 0, 1, 0, 1, 1, 1}, 1 - x], H413m[x_] :> HPL[{0, 0, 0, 1, 1, 0, 0, 1}, 1 - x], H4121m[x_] :> HPL[{0, 0, 0, 1, 1, 0, 1, 1}, 1 - x], H4112m[x_] :> HPL[{0, 0, 0, 1, 1, 1, 0, 1}, 1 - x], H41111m[x_] :> HPL[{0, 0, 0, 1, 1, 1, 1, 1}, 1 - x], H332m[x_] :> HPL[{0, 0, 1, 0, 0, 1, 0, 1}, 1 - x], H3311m[x_] :> HPL[{0, 0, 1, 0, 0, 1, 1, 1}, 1 - x], H3221m[x_] :> HPL[{0, 0, 1, 0, 1, 0, 1, 1}, 1 - x], H3212m[x_] :> HPL[{0, 0, 1, 0, 1, 1, 0, 1}, 1 - x], H32111m[x_] :> HPL[{0, 0, 1, 0, 1, 1, 1, 1}, 1 - x], H3122m[x_] :> HPL[{0, 0, 1, 1, 0, 1, 0, 1}, 1 - x], H31211m[x_] :> HPL[{0, 0, 1, 1, 0, 1, 1, 1}, 1 - x], H31121m[x_] :> HPL[{0, 0, 1, 1, 1, 0, 1, 1}, 1 - x], H31112m[x_] :> HPL[{0, 0, 1, 1, 1, 1, 0, 1}, 1 - x], H311111m[x_] :> HPL[{0, 0, 1, 1, 1, 1, 1, 1}, 1 - x], H22211m[x_] :> HPL[{0, 1, 0, 1, 0, 1, 1, 1}, 1 - x], H22121m[x_] :> HPL[{0, 1, 0, 1, 1, 0, 1, 1}, 1 - x], H221111m[x_] :> HPL[{0, 1, 0, 1, 1, 1, 1, 1}, 1 - x], H212111m[x_] :> HPL[{0, 1, 1, 0, 1, 1, 1, 1}, 1 - x], H2111111m[x_] :> HPL[{0, 1, 1, 1, 1, 1, 1, 1}, 1 - x], Phi6[x_, y_, z_] :> Subscript[OverTilde[\[CapitalPhi]], 6], tPhi6[x_, y_, z_] :> Subscript[OverTilde[\[CapitalPhi]], 6], F1[x_, y_, z_] :> Subscript[F, 1][x, y, z], Omega2t[x_, y_, z_] :> Superscript[\[CapitalOmega], "(2)"][x, y, z], Omega2[x_, y_, z_] :> Superscript[\[CapitalOmega], "(2)"][x, y, z], G[x_, y_, z_] :> G, Nt[x_, y_, z_] :> N, Nfunc[x_, y_, z_] :> N, Ot[x_, y_, z_] :> O, Ofunc[x_, y_, z_] :> O, H[x_, y_, z_] :> Subscript[H, 1][x, y, z], H1[x_, y_, z_] :> Subscript[H, 1][x, y, z], J[x_, y_, z_] :> Subscript[J, 1][x, y, z], J1[x_, y_, z_] :> Subscript[J, 1][x, y, z], K[x_, y_, z_] :> Subscript[K, 1][x, y, z], K1[x_, y_, z_] :> Subscript[K, 1][x, y, z], M1t[x_, y_, z_] :> Subscript[M, 1][x, y, z], M1[x_, y_, z_] :> Subscript[M, 1][x, y, z], Qu[x_, y_, z_] :> Subscript[Q, "ep"][x, y, z], Qep[x_,y_,z_] :> Subscript[Q, "ep"][x, y, z], QU[x_, y_, z_] :> Subscript[Q, "ep"][x, y, z]};
