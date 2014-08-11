(* ::Package:: *)

ClearAll[irreducibleFunctionsToLineE,irreducibleFunctionsToLineM,toLineE,toLineM,toPointE,toPointM]

irreducibleFunctionsToLineE[line_]:={H3[a_]:>toLineE[H3[a],line],H4[a_]:>toLineE[H4[a],line],H5[a_]:>toLineE[H5[a],line],H6[a_]:>toLineE[H6[a],line],H7[a_]:>toLineE[H7[a],line],H8[a_]:>toLineE[H8[a],line],H9[a_]:>toLineE[H9[a],line],H10[a_]:>toLineE[H10[a],line],Subscript[OverTilde[\[CapitalPhi]],6]:>toLineE[Subscript[OverTilde[\[CapitalPhi]],6],line],Superscript[\[CapitalOmega],"(2)"][a_,b_,c_]:>toLineE[Superscript[\[CapitalOmega],"(2)"][a,b,c],line],Subscript[F,1][s_,b_,c_]:>toLineE[Subscript[F,1][s,b,c],line],Subscript[H,1][s_,b_,c_]:>toLineE[Subscript[H,1][s,b,c],line],Subscript[J,1][s_,b_,c_]:>toLineE[Subscript[J,1][s,b,c],line],N:>toLineE[N,line],O:>toLineE[O,line],Subscript[M,1][s_,b_,c_]:>toLineE[Subscript[M,1][s,b,c],line],Subscript[Q,"ep"][a_,b_,c_]:>toLineE[Subscript[Q,"ep"][a,b,c],line],G:>toLineE[G,line],Subscript[K,1][a_,b_,c_]:>toLineE[Subscript[K,1][a,b,c],line]};
irreducibleFunctionsToLineM[line_]:={H3[a_]:>toLineM[H3[a],line],H4[a_]:>toLineM[H4[a],line],H5[a_]:>toLineM[H5[a],line],H6[a_]:>toLineM[H6[a],line],H7[a_]:>toLineM[H7[a],line],H8[a_]:>toLineM[H8[a],line],H9[a_]:>toLineM[H9[a],line],H10[a_]:>toLineM[H10[a],line],Subscript[OverTilde[\[CapitalPhi]],6]:>toLineM[Subscript[OverTilde[\[CapitalPhi]],6],line],Superscript[\[CapitalOmega],"(2)"][a_,b_,c_]:>toLineM[Superscript[\[CapitalOmega],"(2)"][a,b,c],line],Subscript[F,1][s_,b_,c_]:>toLineM[Subscript[F,1][s,b,c],line],Subscript[H,1][s_,b_,c_]:>toLineM[Subscript[H,1][s,b,c],line],Subscript[J,1][s_,b_,c_]:>toLineM[Subscript[J,1][s,b,c],line],N:>toLineM[N,line],O:>toLineM[O,line],Subscript[M,1][s_,b_,c_]:>toLineM[Subscript[M,1][s,b,c],line],Subscript[Q,"ep"][a_,b_,c_]:>toLineM[Subscript[Q,"ep"][a,b,c],line],G:>toLineM[G,line],Subscript[K,1][a_,b_,c_]:>toLineM[Subscript[K,1][a,b,c],line]};

toLineE[func_,line_]:=toLineE[Expand[func],line]/;!MatchQ[func,Expand[func]];
toLineE[func_,line_]:=Sum[toLineE[terms,line],{terms,List@@func}]/;MatchQ[func,Plus[_,__]];
toLineE[Times[func1_,funcN__],line_]:=toLineE[func1,line]toLineE[Times[funcN],line]/;MatchQ[func1,Alternatives@@allIrreducibleFunctions]\[And]!And@@(NumericQ/@List[funcN]);
toLineE[func_,{u,1,1}]:=Expand[IntegrateHPL[Simplify[coproductD[func,u]/.irreducibleFunctionsToLineE[{u,1,1}]/.replace\[CapitalDelta]/.v->1/.w->1,1>u>0],{u,1,u}]]-If[MatchQ[func,Superscript[\[CapitalOmega],"(2)"][_,_,_]],6\[Zeta][4],0]/;!MatchQ[func,Alternatives[Plus[_,__],Times[__,Alternatives@allIrreducibleFunctions]]];
toLineE[func_,{1,v,1}]:=Expand[IntegrateHPL[Simplify[coproductD[func,v]/.irreducibleFunctionsToLineE[{1,v,1}]/.replace\[CapitalDelta]/.u->1/.w->1,1>v>0],{v,1,v}]]-If[MatchQ[func,Superscript[\[CapitalOmega],"(2)"][_,_,_]],6\[Zeta][4],0]/;!MatchQ[func,Alternatives[Plus[_,__],Times[__,Alternatives@allIrreducibleFunctions]]];
toLineE[func_,{1,1,w}]:=Expand[IntegrateHPL[Simplify[coproductD[func,w]/.irreducibleFunctionsToLineE[{1,1,w}]/.replace\[CapitalDelta]/.u->1/.v->1,1>w>0],{w,1,w}]]-If[MatchQ[func,Superscript[\[CapitalOmega],"(2)"][_,_,_]],6\[Zeta][4],0]/;!MatchQ[func,Alternatives[Plus[_,__],Times[__,Alternatives@allIrreducibleFunctions]]];
toLineE[func_,{u,u,1}]:=Module[{functionalForm},functionalForm=IntegrateHPL[ReplaceAll[(coproductEntry[func,u]+coproductEntry[func,v])/u-(coproductEntry[func,1-u]+coproductEntry[func,1-v])/(1-u),irreducibleFunctionsToLineE[{u,u,1}]]/.{v->u}/.toHPL/.flipArgument[w]/.{1-w->Subscript[\[Xi],w]}/.{HPL[{___,1},Subscript[\[Xi],w]]->0},{u,0,u}]; functionalForm-ReplaceAll[functionalForm/.flipArgument[u]/.{1-u->Subscript[\[Xi],u]},HPL[{___,1},Subscript[\[Xi],u]]->0]-If[MatchQ[func,Superscript[\[CapitalOmega],"(2)"][_,_,_]],6\[Zeta][4],0]]/;!MatchQ[func,Alternatives[Plus[_,__],Times[__,Alternatives@allIrreducibleFunctions]]];
toLineE[func_,{1,v,v}]:=Module[{functionalForm},functionalForm=IntegrateHPL[ReplaceAll[(coproductEntry[func,v]+coproductEntry[func,w])/v-(coproductEntry[func,1-v]+coproductEntry[func,1-w])/(1-v),irreducibleFunctionsToLineE[{1,v,v}]]/.{w->v}/.toHPL/.flipArgument[u]/.{1-u->Subscript[\[Xi],u]}/.{HPL[{___,1},Subscript[\[Xi],u]]->0},{v,0,v}]; functionalForm-ReplaceAll[functionalForm/.flipArgument[v]/.{1-v->Subscript[\[Xi],v]},HPL[{___,1},Subscript[\[Xi],v]]->0]-If[MatchQ[func,Superscript[\[CapitalOmega],"(2)"][_,_,_]],6\[Zeta][4],0]]/;!MatchQ[func,Alternatives[Plus[_,__],Times[__,Alternatives@allIrreducibleFunctions]]];
toLineE[func_,{w,1,w}]:=Module[{functionalForm},functionalForm=IntegrateHPL[ReplaceAll[(coproductEntry[func,w]+coproductEntry[func,u])/w-(coproductEntry[func,1-w]+coproductEntry[func,1-u])/(1-w),irreducibleFunctionsToLineE[{w,1,w}]]/.{u->w}/.toHPL/.flipArgument[v]/.{1-v->Subscript[\[Xi],v]}/.{HPL[{___,1},Subscript[\[Xi],v]]->0},{w,0,w}]; functionalForm-ReplaceAll[functionalForm/.flipArgument[w]/.{1-w->Subscript[\[Xi],w]},HPL[{___,1},Subscript[\[Xi],w]]->0]-If[MatchQ[func,Superscript[\[CapitalOmega],"(2)"][_,_,_]],6\[Zeta][4],0]]/;!MatchQ[func,Alternatives[Plus[_,__],Times[__,Alternatives@allIrreducibleFunctions]]];

toLineM[func_,{u,1,1}]:=Expand[toLineE[func,{u,1,1}]/.{HPL[{0},u]->HPL[{0},u]-2Pi I}];
toLineM[func_,{1,v,1}]:=Expand[toLineE[func,{1,v,1}]/.{HPL[{0},v]->HPL[{0},v]-2Pi I}];
toLineM[func_,{1,1,w}]:=Expand[toLineE[func,{1,1,w}]/.{HPL[{0},w]->HPL[{0},w]-2Pi I}];
toLineM[func_,{u,u,1}]:=Module[{functionalForm},functionalForm=IntegrateHPL[Expand[(coproductEntry[func,u]+coproductEntry[func,v])/u-(coproductEntry[func,1-u]+coproductEntry[func,1-v])/(1-u)]/.toHPL/.flipArgument[1-w]/.{HPL[{0},w]->HPL[{0},w]-2Pi I}/.flipArgument[w]/.irreducibleFunctionsToLineM[{u,u,1}]/.{v->u}/.flipArgument[w]/.{1-w->Subscript[\[Xi],w]}/.{HPL[{___,1},Subscript[\[Xi],w]]->0},{u,0,u}]; functionalForm-ReplaceAll[functionalForm/.flipArgument[u]/.{1-u->Subscript[\[Xi],u]},HPL[{___,1},Subscript[\[Xi],u]]->0]+toPointM[func,{1,1,w},w->1]];
toLineM[func_,{1,v,v}]:=Module[{functionalForm},functionalForm=IntegrateHPL[Expand[(coproductEntry[func,v]+coproductEntry[func,w])/v-(coproductEntry[func,1-v]+coproductEntry[func,1-w])/(1-v)]/.toHPL/.flipArgument[1-u]/.{HPL[{0},u]->HPL[{0},u]-2Pi I}/.flipArgument[u]/.irreducibleFunctionsToLineM[{1,v,v}]/.{w->v}/.flipArgument[u]/.{1-u->Subscript[\[Xi],u]}/.{HPL[{___,1},Subscript[\[Xi],u]]->0},{v,0,v}]; functionalForm-ReplaceAll[functionalForm/.flipArgument[v]/.{1-v->Subscript[\[Xi],v]},HPL[{___,1},Subscript[\[Xi],v]]->0]+toPointM[func,{u,1,1},u->1]];
toLineM[func_,{w,1,w}]:=Module[{functionalForm},functionalForm=IntegrateHPL[Expand[(coproductEntry[func,w]+coproductEntry[func,u])/w-(coproductEntry[func,1-w]+coproductEntry[func,1-u])/(1-w)]/.toHPL/.flipArgument[1-v]/.{HPL[{0},v]->HPL[{0},v]-2Pi I}/.flipArgument[v]/.irreducibleFunctionsToLineM[{w,1,w}]/.{u->w}/.flipArgument[v]/.{1-v->Subscript[\[Xi],v]}/.{HPL[{___,1},Subscript[\[Xi],v]]->0},{w,0,w}]; functionalForm-ReplaceAll[functionalForm/.flipArgument[w]/.{1-w->Subscript[\[Xi],w]},HPL[{___,1},Subscript[\[Xi],w]]->0]+toPointM[func,{1,v,1},v->1]];

toPointE[func_,{u,u,1},u->0]:=toLineE[func,{u,u,1}]/.{HPL[{___,1},u]->0};
toPointE[func_,{1,v,v},v->0]:=toLineE[func,{1,v,v}]/.{HPL[{___,1},v]->0};
toPointE[func_,{w,1,w},w->0]:=toLineE[func,{w,1,w}]/.{HPL[{___,1},w]->0};

toPointM[func_,{u,1,1},u->1]:=Expand[toLineM[func,{u,1,1}]/.flipArgument[u]/.{1-u->Subscript[\[Xi],u]}/.HPL[{___,1},Subscript[\[Xi],u]]->0];
toPointM[func_,{1,v,1},v->1]:=Expand[toLineM[func,{1,v,1}]/.flipArgument[v]/.{1-v->Subscript[\[Xi],v]}/.HPL[{___,1},Subscript[\[Xi],v]]->0];
toPointM[func_,{1,1,w},w->1]:=Expand[toLineM[func,{1,1,w}]/.flipArgument[w]/.{1-w->Subscript[\[Xi],w]}/.HPL[{___,1},Subscript[\[Xi],w]]->0];
toPointM[func_,{u,u,1},u->0]:=Expand[toLineM[func,{u,u,1}]/.{HPL[{___,1},u]->0}];
toPointM[func_,{1,v,v},v->0]:=Expand[toLineM[func,{1,v,v}]/.{HPL[{___,1},v]->0}];
toPointM[func_,{w,1,w},w->0]:=Expand[toLineM[func,{w,1,w}]/.{HPL[{___,1},w]->0}];