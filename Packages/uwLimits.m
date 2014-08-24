(* ::Package:: *)

irreducibleDSFunctionsToLineE[line_]:={DS3[a_]:>toDSLineE[DS3[a],line],DS4[a_]:>toDSLineE[DS4[a],line],DS5[a_]:>toDSLineE[DS5[a],line],DS6[a_]:>toDSLineE[DS6[a],line],DS7[a_]:>toDSLineE[DS7[a],line],DS8[a_]:>toDSLineE[DS8[a],line],DS9[a_]:>toDSLineE[DS9[a],line],DS10[a_]:>toDSLineE[DS10[a],line]};
irreducibleDSFunctionsToZero={DS3[a_]:>0,DS4[a_]:>0,DS5[a_]:>0,DS6[a_]:>0,DS7[a_]:>0,DS8[a_]:>0,DS9[a_]:>0,DS10[a_]:>0};

toDSLineE[func_,line_]:=toDSLineE[Expand[func],line]/;!MatchQ[func,Expand[func]];
toDSLineE[func_,line_]:=Expand[Sum[toDSLineE[terms,line],{terms,List@@func}]/;MatchQ[func,Plus[_,__]]];
toDSLineE[Times[func1_,funcN__],line_]:=toDSLineE[func1,line]toDSLineE[Times[funcN],line]/;MatchQ[func1,Alternatives@@allIrreducibleFunctions]\[And]!And@@(NumericQ/@List[funcN]);
toDSLineE[func_,{u,1}]:=IntegrateHPL[coproductD[func,u]/.w->1/.irreducibleDSFunctionsToLineE[{u,1}],{u,1,u}]+ReplaceAll[func,Join[irreducibleDSFunctionsToZero,{CircleDot[__]->0,u->1,w->1}]];
toDSLineE[func_,{1,w}]:=IntegrateHPL[coproductD[func,w]/.u->1/.irreducibleDSFunctionsToLineE[{1,w}],{w,1,w}]+ReplaceAll[func,Join[irreducibleDSFunctionsToZero,{CircleDot[__]->0,u->1,w->1}]];
toDSLineE[func_,{u,1-u}]:=toDSPointE[func,{u,1},u->0]+IntegrateHPL[(coproductD[func,u]-coproductD[func,w])/.{w->1-u}/.irreducibleDSFunctionsToLineE[{u,1-u}],{u,0,u}];

toDSPointE[func_,{u,1},u->0]:=toDSLineE[func,{u,1}]/.flipArgument[1-u]/.{HPL[{___,1},u]->0}/.toLogs/.u->U;
toDSPointE[func_,{1,w},w->0]:=toDSLineE[func,{1,w}]/.flipArgument[1-w]/.{HPL[{___,1},w]->0}/.toLogs/.w->W;
