(* ::Package:: *)

irreducibleDoubleScalingFunctionsToLineE[line_]:={DS3[a_]:>toLineE[DS3[a],line],DS4[a_]:>toLineE[DS4[a],line],DS5[a_]:>toLineE[DS5[a],line],DS6[a_]:>toLineE[DS6[a],line],DS7[a_]:>toLineE[DS7[a],line],DS8[a_]:>toLineE[DS8[a],line],DS9[a_]:>toLineE[DS9[a],line],DS10[a_]:>toLineE[DS10[a],line]};

toLineE[DS3[a_],line_]:=Module[{},toLineE[DS3[temp1_],temp2_]=.;
  toLineE[DS4[temp1_],temp2_]=.;
  toLineE[DS5[temp1_],temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Double Scaling Limits/Local Binaries/weight_5_ds_euclidean_lines_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 5 double scaling euclidean lines loaded"]];
  toLineE[DS3[a],line]];
toLineE[DS4[a_],line_]:=Module[{},toLineE[DS3[temp1_],temp2_]=.;
  toLineE[DS4[temp1_],temp2_]=.;
  toLineE[DS5[temp1_],temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Double Scaling Limits/Local Binaries/weight_5_ds_euclidean_lines_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 5 double scaling euclidean lines loaded"]];
  toLineE[DS4[a],line]];
toLineE[DS5[a_],line_]:=Module[{},toLineE[DS3[temp1_],temp2_]=.;
  toLineE[DS4[temp1_],temp2_]=.;
  toLineE[DS5[temp1_],temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Double Scaling Limits/Local Binaries/weight_5_ds_euclidean_lines_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 5 double scaling euclidean lines loaded"]];
  toLineE[DS5[a],line]];
toLineE[DS6[a_],line_]:=Module[{},toLineE[DS6[temp1_],temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Double Scaling Limits/Local Binaries/weight_6_ds_euclidean_lines_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 6 double scaling euclidean lines loaded"]];
  toLineE[DS6[a],line]];
toLineE[DS7[a_],line_]:=Module[{},toLineE[DS7[temp1_],temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Double Scaling Limits/Local Binaries/weight_7_ds_euclidean_lines_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 7 double scaling euclidean lines loaded"]];
  toLineE[DS7[a],line]];
toLineE[DS8[a_],line_]:=Module[{},toLineE[DS8[temp1_],temp2_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Double Scaling Limits/Local Binaries/weight_8_ds_euclidean_lines_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["weight 8 double scaling euclidean lines loaded"]];
  toLineE[DS8[a],line]];

(*toLineE[func_,{1,0,w}]:=(toLineE[func,{1,0,w}]=toLineE[toSurfaceE[func,v->0],{1,0,w}])/;!FreeQ[func,Alternatives[H3[_],H4[_],H5[_],H6[_],E7[_],O7[_],E8[_],O8[_],E9[_],O9[_]]];*)

toLineE[func_,{u,0,1}]:=(toLineE[func,{u,0,1}]=Expand[func/.irreducibleDoubleScalingFunctionsToLineE[{u,0,1}]/.flipArgument[w]/.{HPL[{___,1},1-w]->0,HPL[{0},w]->Log[w]}])/;FreeQ[func,Alternatives[H3[_],H4[_],H5[_],H6[_],E7[_],O7[_],E8[_],O8[_],E9[_],O9[_]]];
toLineE[func_,{1,0,w}]:=(toLineE[func,{1,0,w}]=Expand[func/.irreducibleDoubleScalingFunctionsToLineE[{1,0,w}]/.flipArgument[u]/.{HPL[{___,1},1-u]->0,HPL[{0},u]->Log[u]}])/;FreeQ[func,Alternatives[H3[_],H4[_],H5[_],H6[_],E7[_],O7[_],E8[_],O8[_],E9[_],O9[_]]];
toLineE[func_,{u,0,1-u}]:=(toLineE[func,{u,0,1-u}]:=Expand[func/.irreducibleDoubleScalingFunctionsToLineE[{u,0,1-u}]/.{w->1-u}/.flipArgument[1-u]])/;FreeQ[func,Alternatives[H3[_],H4[_],H5[_],H6[_],E7[_],O7[_],E8[_],O8[_],E9[_],O9[_]]];
toLineE[func_,{u,0,0}]:=(toLineE[func,{u,0,0}]=Expand[func/.irreducibleDoubleScalingFunctionsToLineE[{u,0,0}]/.flipArgument[{1-u,1-w}]/.HPL[{___,1},w]->0/.HPL[{0},a_]:>Log[a]])/;FreeQ[func,Alternatives[H3[_],H4[_],H5[_],H6[_],E7[_],O7[_],E8[_],O8[_],E9[_],O9[_]]];

toLineEc[func_,{u,0,1}]:=toLineEc[func,{u,0,1}]=Expand[IntegrateHPL[coproductD[func,u]/.irreducibleDoubleScalingFunctionsToLineE[{u,0,1}]/.Power[1-u-w,-1]->Power[-u,-1]/.flipArgument[w]/.{HPL[{___,1},1-w]->0,HPL[{0},1-w]->Log[1-w]},{u,1,u}]];
toLineEc[func_,{1,0,w}]:=toLineEc[func,{1,0,w}]=Expand[IntegrateHPL[coproductD[func,w]/.irreducibleDoubleScalingFunctionsToLineE[{1,0,w}]/.Power[1-u-w,-1]->Power[-w,-1]/.flipArgument[u]/.{HPL[{___,1},1-u]->0,HPL[{0},1-u]->Log[1-u]},{w,1,w}]];
toLineEc[func_,{u,0,1-u}]:=toLineEc[func,{u,0,1-u}]=Module[{functionalForm}, functionalForm=Expand[IntegrateHPL[Expand[(coproductD[func,u]-coproductD[func,w])/.{w->1-u}/.irreducibleDoubleScalingFunctionsToLineE[{u,0,1-u}]/.flipArgument[1-u]],{u,0,u}]]; Expand[functionalForm+toPointE[func,{u,0,1},u->0]-(functionalForm/.HPL[{___,1},u]->0)]];
toLineEc[func_,{u,0,0}]:=toLineEc[func,{u,0,0}]=Module[{functionalForm}, functionalForm=Expand[IntegrateHPL[coproductD[func,u]/.irreducibleDoubleScalingFunctionsToLineE[{u,0,0}]/.flipArgument[1-w]/.HPL[{___,1},w]->0/.Power[1-u-w,-1]->Power[1-u,-1],{u,1,u}]]; Expand[(functionalForm+toPointE[func,{1,0,w},w->0]-(functionalForm/.flipArgument[u]/.HPL[{___,1},1-u]->0))/.flipArgument[{1-u,1-v,1-w}]/.HPL[{0},a_]:>Log[a]]];

toPointE[func_,{u,0,1},u->0]:=toLineE[func,{u,0,1}]/.flipArgument[1-u]/.{HPL[{___,1},u]->0};
toPointE[func_,{1,0,w},w->0]:=toLineE[func,{1,0,w}]/.flipArgument[1-w]/.{HPL[{___,1},w]->0};
