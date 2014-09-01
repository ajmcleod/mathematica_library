(* ::Package:: *)

<<MRKansatz.dat;
If[useLJfunctions==True,Get["MRK_limits_irreducible_basis_functions.dat"];Get["EMRK_limits_irreducible_basis_functions.dat"],Get["MRK_limits_irreducible_functions.dat"];Get["EMRK_limits_irreducible_functions.dat"]];

irreducibleFunctionsToEMRK[limit_] := {H3[a_] :> EMRK[H3[a],limit], H4[a_] :> EMRK[H4[a],limit], H5[a_] :> EMRK[H5[a],limit], H6[a_] :> EMRK[H6[a],limit], H7[a_] :> EMRK[H7[a],limit], H8[a_] :> EMRK[H8[a],limit], H9[a_] :> EMRK[H9[a],limit], H10[a_] :> EMRK[H10[a],limit], Subscript[OverTilde[\[CapitalPhi]],6]:>EMRK[Subscript[OverTilde[\[CapitalPhi]],6],limit], Superscript[\[CapitalOmega], "(2)"][a_,b_,c_]:> EMRK[Superscript[\[CapitalOmega], "(2)"][a,b,c],limit], Subscript[F, 1][s_,b_,c_]:>EMRK[Subscript[F, 1][s,b,c],limit],Subscript[H, 1][s_,b_,c_]:>EMRK[Subscript[H, 1][s,b,c],limit], Subscript[J, 1][s_,b_,c_]:>EMRK[Subscript[J, 1][s,b,c],limit],N :>EMRK[N,limit], O :> EMRK[O,limit],  Subscript[M, 1][s_,b_,c_]:>EMRK[Subscript[M, 1][s,b,c],limit], Subscript[Q, "ep"][a_, b_, c_] :> EMRK[Subscript[Q, "ep"][a, b, c],limit], G :> EMRK[G,limit], Subscript[K, 1][a_, b_, c_]:>EMRK[Subscript[K, 1][a, b, c],limit]};
irreducibleFunctionsToMRK = {H3[a_] :> MRK[H3[a]], H4[a_] :> MRK[H4[a]], H5[a_] :> MRK[H5[a]], H6[a_] :> MRK[H6[a]], H7[a_] :> MRK[H7[a]], H8[a_] :> MRK[H8[a]], H9[a_] :> MRK[H9[a]], H10[a_] :> MRK[H10[a]], Subscript[OverTilde[\[CapitalPhi]],6]:>MRK[Subscript[OverTilde[\[CapitalPhi]],6]], Superscript[\[CapitalOmega], "(2)"][a_,b_,c_]:> MRK[Superscript[\[CapitalOmega], "(2)"][a,b,c]], Subscript[F, 1][s_,b_,c_]:>MRK[Subscript[F, 1][s,b,c]],Subscript[H, 1][s_,b_,c_]:>MRK[Subscript[H, 1][s,b,c]], Subscript[J, 1][s_,b_,c_]:>MRK[Subscript[J, 1][s,b,c]],N :>MRK[N], O :> MRK[O],  Subscript[M, 1][s_,b_,c_]:>MRK[Subscript[M, 1][s,b,c]], Subscript[Q, "ep"][a_, b_, c_] :> MRK[Subscript[Q, "ep"][a, b, c]], G :> MRK[G], Subscript[K, 1][a_, b_, c_]:>MRK[Subscript[K, 1][a, b, c]]};
(*irreducibleFunctionsToMRK[limit_] := {H3[a_] :> MRK[H3[a],limit], H4[a_] :> MRK[H4[a],limit], H5[a_] :> MRK[H5[a],limit], H6[a_] :> MRK[H6[a],limit], H7[a_] :> MRK[H7[a],limit], H8[a_] :> MRK[H8[a],limit], H9[a_] :> MRK[H9[a],limit], H10[a_] :> MRK[H10[a],limit], Subscript[OverTilde[\[CapitalPhi]],6]:>MRK[Subscript[OverTilde[\[CapitalPhi]],6],limit], Superscript[\[CapitalOmega], "(2)"][a_,b_,c_]:> MRK[Superscript[\[CapitalOmega], "(2)"][a,b,c],limit], Subscript[F, 1][s_,b_,c_]:>MRK[Subscript[F, 1][s,b,c],limit],Subscript[H, 1][s_,b_,c_]:>MRK[Subscript[H, 1][s,b,c],limit], Subscript[J, 1][s_,b_,c_]:>MRK[Subscript[J, 1][s,b,c],limit],N :>MRK[N,limit], O :> MRK[O,limit],  Subscript[M, 1][s_,b_,c_]:>MRK[Subscript[M, 1][s,b,c],limit], Subscript[Q, "ep"][a_, b_, c_] :> MRK[Subscript[Q, "ep"][a, b, c],limit], G :> MRK[G,limit], Subscript[K, 1][a_, b_, c_]:>MRK[Subscript[K, 1][a, b, c],limit]};*)

toEMRKlimit[func_,varTo1_->1]:=Block[{u1=varTo1,u2=varTo1/.cycle,u3=varTo1/.cycle/.cycle},Expand[func/.irreducibleFunctionsToEMRK[u1->1]/.SVHPLreplacements/.{Subscript[z,u1]->z,Subscript[zb,u1]->zb}/.{Log[Subscript[\[Xi],_]]:>HPL[{0},\[Xi]]}/.toHPL/.{u1->1-\[Xi]}/.flipArgument[{1-u2,1-u3,1-\[Xi]}]/.HPL[{___,1},Alternatives[\[Xi],u2,u3]]->0/.{HPL[{0},\[Xi]]->Log[\[Xi]], HPL[{0},u2]->Log[\[Xi]]+HPL[{1},z]+HPL[{1},zb], HPL[{0},u3]->Log[\[Xi]]+HPL[{0},z]+HPL[{0},zb]+HPL[{1},z]+HPL[{1},zb]}]];
toMRKlimit[func_]:=Expand[func/.irreducibleFunctionsToMRK/.SVHPLreplacements/.{Log[\[Xi]]->HPL[{0},\[Xi]]}/.toHPL/.flipArgument[{1-u,1-v,1-w}]/.{HPL[{0},u]->HPL[{0},u]-2Pi I}/.flipArgument[u]/.{u->1-\[Xi]}/.HPL[{___,1},Alternatives[\[Xi],v,w]]->0/.{HPL[{0},\[Xi]]->Log[\[Xi]], HPL[{0},v]->Log[\[Xi]]+HPL[{1},z]+HPL[{1},zb], HPL[{0},w]->Log[\[Xi]]+HPL[{0},z]+HPL[{0},zb]+HPL[{1},z]+HPL[{1},zb]}];

toMRK[func_]:=Block[{weight,SVHPLtermsWeight,coefficients,HPLbasis,ansatz,zDiffInMRKlimit,zEqns,zSolutionReplacements,pure\[Xi]terms,zSolutionFunc,integrationConstant,zLimitMatching,MRKfunc},
	weight=transcendentalWeight[func];
	SVHPLtermsWeight[n_]:=Get["weight_"<>ToString[n]<>"_SVHPL_basis.dat"];
	coefficients=Flatten@Table[Table[c[w,i],{i,Length[SVHPLtermsWeight[w]]}],{w,weight}];
	HPLbasis=Flatten[Table[HPL[word,var],{word,generateLyndonBasis[weight-1,{0,1}]},{var,{z,zb}}]];
	ansatz=Sum[MRKansatzWeight[i],{i,weight}];
	zDiffInMRKlimit = toMRKlimit[coproductD[func,z]];
	zEqns=DeleteCases[Flatten[Normal[CoefficientArrays[(Expand[zDiffInMRKlimit/.SVHPLreplacements]-ansatz)/.flipArgument[{1-z,1-zb}]/.{1/z->zInv,1/(1-z)->zFlipInv},Join[HPLbasis,{zInv,zFlipInv}]]]],0];
	zSolutionReplacements=List@@Reduce[zEqns==ConstantArray[0,Length[zEqns]],coefficients]/.Equal[x_,y_]:>Rule[x,y];
	zSolutionFunc=Sum[Sum[c[w,i]SVHPLtermsWeight[w][[i]],{i,Length[SVHPLtermsWeight[w]]}],{w,weight}]/.zSolutionReplacements;
	zLimitMatching=Expand[ReplaceAll[toPointM[func,{1,v,v},v->0]/.toLogs,Log[v]->Log[\[Xi]]-HPL[{0},1-z]-HPL[{0},1-zb]]-ReplaceAll[zSolutionFunc/.SVHPLreplacements/.flipArgument[{z,zb}],HPL[{___,1},1-Alternatives[z,zb]]->0]];
	MRKfunc=Expand[Expand[zSolutionFunc+zLimitMatching]/.{Pi^3->6 Pi \[Zeta][2],Pi^5->90 Pi \[Zeta][4]}];
	checkMRK\[Xi]D[func,MRKfunc];
	MRKfunc]

toEMRK[0,limit_]:=0;
toEMRK[func_,limit_:(u->1)]:=Block[{weight,SVHPLtermsWeight,coefficients,HPLbasis,ansatz,zDiffInMRKlimit,zEqns,zSolutionReplacements,pure\[Xi]terms,zSolutionFunc,integrationConstant,zLimitMatching,EMRKfunc,u1=limit/.Rule[x_,_]:>x,u2=limit/.Rule[x_,_]:>x/.cycle,u3=limit/.Rule[x_,_]:>x/.cycle/.cycle},
	weight=transcendentalWeight[func];
	SVHPLtermsWeight[n_]:=Get["weight_"<>ToString[n]<>"_SVHPL_basis.dat"];
	coefficients=Flatten@Table[Table[c[w,i],{i,Length[SVHPLtermsWeight[w]]}],{w,weight}];
	HPLbasis=Flatten[Table[HPL[word,var],{word,generateLyndonBasis[weight-1,{0,1}]},{var,{z,zb}}]];
	ansatz=Sum[MRKansatzWeight[i],{i,weight}];
	zDiffInMRKlimit=toEMRKlimit[coproductD[func,Subscript[z,u1]],limit];
	zEqns=DeleteCases[Flatten[Normal[CoefficientArrays[(Expand[zDiffInMRKlimit/.SVHPLreplacements]-ansatz)/.flipArgument[{1-z,1-zb}]/.{1/z->zInv,1/(1-z)->zFlipInv},Join[HPLbasis,{zInv,zFlipInv}]]]],0];
	zSolutionReplacements=List@@Reduce[zEqns==ConstantArray[0,Length[zEqns]],coefficients]/.Equal[x_,y_]:>Rule[x,y];
	zSolutionFunc=Sum[Sum[c[w,i]SVHPLtermsWeight[w][[i]],{i,Length[SVHPLtermsWeight[w]]}],{w,weight}]/.zSolutionReplacements;
	zLimitMatching=Expand[ReplaceAll[toPointE[func,Which[u2===u,{u,u,1},u2===v,{1,v,v},u2===w,{w,1,w}],u2->0]/.toLogs,Log[u2]->Log[\[Xi]]-HPL[{0},1-z]-HPL[{0},1-zb]]-ReplaceAll[zSolutionFunc/.SVHPLreplacements/.flipArgument[{z,zb}],HPL[{___,1},1-Alternatives[z,zb]]->0]];
	EMRKfunc=Expand[Expand[zSolutionFunc+zLimitMatching]/.{SVHPL[x_]->Subscript[SVHPL,u1][x],\[Xi]->Subscript[\[Xi],u1]}/.{Pi^3->6 Pi \[Zeta][2],Pi^5->90 Pi \[Zeta][4]}];
	checkEMRK\[Xi]D[func,EMRKfunc,limit];
	EMRKfunc]/;EvenQ[yGrading[func]];
toEMRK[func_,limit_:(u->1)]:=Block[{weight,SVHPLtermsWeight,coefficients,ansatz,zDiffInMRKlimit,zEqns,zSolutionReplacements,pure\[Xi]terms,zSolutionFunc,integrationConstant,zLimitMatching,EMRKfunc,u1=limit/.Rule[x_,_]:>x,u2=limit/.Rule[x_,_]:>x/.cycle,u3=limit/.Rule[x_,_]:>x/.cycle/.cycle},
	weight=transcendentalWeight[func];
	SVHPLtermsWeight[n_]:=Get["weight_"<>ToString[n]<>"_SVHPL_basis.dat"];
	coefficients={c[1,1],c[1,2]};
	ansatz=MRKansatzWeight[1];
	zDiffInMRKlimit=toEMRKlimit[coproductD[func,Subscript[z,u1]],limit];
	zEqns=DeleteCases[Flatten[Normal[CoefficientArrays[(Expand[zDiffInMRKlimit/.SVHPLreplacements]-ansatz)/.flipArgument[{1-z,1-zb}]/.{1/z->zInv,1/(1-z)->zFlipInv},{zInv,zFlipInv}]]],0];
	zSolutionReplacements=List@@Reduce[zEqns==ConstantArray[0,Length[zEqns]],coefficients]/.Equal[x_,y_]:>Rule[x,y];
	zSolutionFunc=Sum[c[1,i]SVHPLtermsWeight[1][[i]],{i,Length[SVHPLtermsWeight[1]]}]/.zSolutionReplacements;
	zLimitMatching=Expand[ReplaceAll[toPointE[func,Which[u2===u,{u,u,1},u2===v,{1,v,v},u2===w,{w,1,w}],u2->0]/.toLogs,Log[u2]->Log[\[Xi]]-HPL[{0},1-z]-HPL[{0},1-zb]]-ReplaceAll[zSolutionFunc/.SVHPLreplacements/.flipArgument[{z,zb}],HPL[{___,1},1-Alternatives[z,zb]]->0]];
	EMRKfunc=Expand[Expand[zSolutionFunc+zLimitMatching]/.{SVHPL[x_]->Subscript[SVHPL,u1][x],\[Xi]->Subscript[\[Xi],u1]}/.{Pi^3->6 Pi \[Zeta][2],Pi^5->90 Pi \[Zeta][4]}];
	checkEMRK\[Xi]D[func,EMRKfunc,limit];
	EMRKfunc]/;OddQ[yGrading[func]];

checkMRK\[Xi]D[funcCoproduct_,funcMRK_]:=Block[{coproductRepresentationD,MRKrepresentationD},
	coproductRepresentationD =Expand[coproductD[funcCoproduct,\[Xi]]/.irreducibleFunctionsToMRK/.SVHPLreplacements/.toHPL/.flipArgument[1-u]/.HPL[{0},u]->HPL[{0},u]-2Pi I/.{u->1-\[Xi]}/.flipArgument[{1-\[Xi],1-v,1-w}]/.{HPL[{___,1},Alternatives[\[Xi],v,w]]->0,HPL[{0},\[Xi]]->Log[\[Xi]]}/.{HPL[{0},v]->Log[\[Xi]]+HPL[{1},z]+HPL[{1},zb]}/.{HPL[{0},w]->Log[\[Xi]]+HPL[{1},z]+HPL[{1},zb]+HPL[{0},z]+HPL[{0},zb]}/.\[Zeta][x_]:>Zeta[x]];
	MRKrepresentationD=Expand[D[funcMRK/.SVHPLreplacements,\[Xi]]/.\[Zeta][x_]:>Zeta[x]];
	If[Simplify[Expand[coproductRepresentationD-MRKrepresentationD]]=!=0, Print["\[Xi] derivative of ",func," in MRK representation does not match"]]];

checkEMRK\[Xi]D[funcCoproduct_,funcEMRK_,1->varTo1_]:=Block[{coproductRepresentationD,EMRKrepresentationD,u1=varTo1,u2=varTo1/.cycle,u3=varTo1/.cycle/.cycle},
	coproductRepresentationD =Expand[coproductD[funcCoproduct,Subscript[\[Xi],u1]]/.irreducibleFunctionsToEMRK[1->u1]/.SVHPLreplacements/.toHPL/.{u1->1-Subscript[\[Xi],u1]}/.flipArgument[{1-Subscript[\[Xi],u1],1-u2,1-u3}]/.{HPL[{___,1},Alternatives[Subscript[\[Xi],u1],u2,u3]]->0,HPL[{0},Subscript[\[Xi],u1]]->Log[Subscript[\[Xi],u1]]}/.{HPL[{0},u2]->Log[Subscript[\[Xi],u1]]+HPL[{1},Subscript[z,u1]]+HPL[{1},Subscript[zb,u1]]}/.{HPL[{0},u3]->Log[Subscript[\[Xi],u1]]+HPL[{1},Subscript[z,u1]]+HPL[{1},Subscript[zb,u1]]+HPL[{0},Subscript[z,u1]]+HPL[{0},Subscript[zb,u1]]}/.\[Zeta][x_]:>Zeta[x]];
	EMRKrepresentationD=Expand[D[funcEMRK/.SVHPLreplacements,Subscript[\[Xi],u1]]/.\[Zeta][x_]:>Zeta[x]];
	If[Simplify[Expand[coproductRepresentationD-EMRKrepresentationD]]=!=0, Print["\[Xi] derivative of ",func," in EMRK representation does not match"]]]
