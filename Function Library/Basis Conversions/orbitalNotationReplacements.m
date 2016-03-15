(* ::Package:: *)

toOrbitalNotationDS[\[CurlyKappa]1_,\[CurlyKappa]2_]:=expression_:>optimizeOrbitalNotationReplacementsDS[expression][\[CurlyKappa]1,\[CurlyKappa]2]
toOrbitalNotationDT[\[CurlyKappa]1_,\[CurlyKappa]2_]:=expression_:>optimizeOrbitalNotationReplacementsDT[expression][\[CurlyKappa]1,\[CurlyKappa]2]
toOrbitalNotationSP[\[CurlyKappa]1_,\[CurlyKappa]2_]:=expression_:>optimizeOrbitalNotationReplacementsSP[expression][\[CurlyKappa]1,\[CurlyKappa]2]

optimizeOrbitalNotationReplacementsDS[expression_][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{weightsAppearing=DeleteCases[Table[If[!FreeQ[expression,Symbol["DS"<>ToString[ii]]],ii,{}],{ii,3,8}],{}]},
  expression/.Join@@Table[orbitalNotationReplacements[Symbol["DS"<>ToString[ii]]][\[CurlyKappa]1,\[CurlyKappa]2],{ii,weightsAppearing}]]
optimizeOrbitalNotationReplacementsDT[expression_][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{weightsAppearing=DeleteCases[Table[If[!FreeQ[expression,Symbol["DT"<>ToString[ii]]],ii,{}],{ii,3,8}],{}]},
  expression/.Join@@Table[orbitalNotationReplacements[Symbol["DT"<>ToString[ii]]][\[CurlyKappa]1,\[CurlyKappa]2],{ii,weightsAppearing}]]
optimizeOrbitalNotationReplacementsSP[expression_][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{weightsAppearing=DeleteCases[Table[If[!FreeQ[expression,Symbol["SP"<>ToString[ii]]],ii,{}],{ii,3,8}],{}]},
  expression/.Join@@Table[orbitalNotationReplacements[Symbol["SP"<>ToString[ii]]][\[CurlyKappa]1,\[CurlyKappa]2],{ii,weightsAppearing}]]

orbitalNotationReplacements[DS3][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{DS3,DS4,DS5,DS6,DS7,DS8}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_DS_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for DS functions"]];
  orbitalNotationReplacements[DS3][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[DS4][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{DS3,DS4,DS5,DS6,DS7,DS8}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_DS_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for DS functions"]];
  orbitalNotationReplacements[DS4][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[DS5][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{DS3,DS4,DS5,DS6,DS7,DS8}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_DS_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for DS functions"]];
  orbitalNotationReplacements[DS5][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[DS6][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{DS3,DS4,DS5,DS6,DS7,DS8}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_DS_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for DS functions"]];
  orbitalNotationReplacements[DS6][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[DS7][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{DS3,DS4,DS5,DS6,DS7,DS8}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_DS_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for DS functions"]];
  orbitalNotationReplacements[DS7][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[DS8][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{DS3,DS4,DS5,DS6,DS7,DS8}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_DS_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for DS functions"]];
  orbitalNotationReplacements[DS8][\[CurlyKappa]1,\[CurlyKappa]2]];

orbitalNotationReplacements[DT3][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{DT3,DT4,DT5,DT6,DT7,DT8}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_DT_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for DT functions"]];
  orbitalNotationReplacements[DT3][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[DT4][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{DT3,DT4,DT5,DT6,DT7,DT8}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_DT_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for DT functions"]];
  orbitalNotationReplacements[DT4][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[DT5][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{DT3,DT4,DT5,DT6,DT7,DT8}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_DT_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for DT functions"]];
  orbitalNotationReplacements[DT5][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[DT6][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{DT3,DT4,DT5,DT6,DT7,DT8}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_DT_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for DT functions"]];
  orbitalNotationReplacements[DT6][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[DT7][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{DT3,DT4,DT5,DT6,DT7,DT8}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_DT_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for DT functions"]];
  orbitalNotationReplacements[DT7][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[DT8][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{DT3,DT4,DT5,DT6,DT7,DT8}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_DT_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for DT functions"]];
  orbitalNotationReplacements[DT8][\[CurlyKappa]1,\[CurlyKappa]2]];

orbitalNotationReplacements[SP2][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{SP2,SP3,SP4,SP5,SP6,SP7}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_SP_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for SP functions"]];
  orbitalNotationReplacements[SP3][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[SP3][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{SP2,SP3,SP4,SP5,SP6,SP7}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_SP_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for SP functions"]];
  orbitalNotationReplacements[SP3][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[SP4][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{SP2,SP3,SP4,SP5,SP6,SP7}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_SP_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for SP functions"]];
  orbitalNotationReplacements[SP4][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[SP5][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{SP2,SP3,SP4,SP5,SP6,SP7}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_SP_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for SP functions"]];
  orbitalNotationReplacements[SP5][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[SP6][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{SP2,SP3,SP4,SP5,SP6,SP7}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_SP_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for SP functions"]];
  orbitalNotationReplacements[SP6][\[CurlyKappa]1,\[CurlyKappa]2]];
orbitalNotationReplacements[SP7][\[CurlyKappa]1_,\[CurlyKappa]2_]:=Module[{},Do[orbitalNotationReplacements[functions][temp1_,temp2_]=.,{functions,{SP2,SP3,SP4,SP5,SP6,SP7}}];
  Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/Local Binaries/orbitalNotationReplacements_SP_10.mx"];
  If[debug,Print["orbitalNotationReplacements loaded for SP functions"]];
  orbitalNotationReplacements[SP7][\[CurlyKappa]1,\[CurlyKappa]2]];
