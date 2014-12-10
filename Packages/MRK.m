(* ::Package:: *)

<<SVHPL.m;
<<"EMRKansatz.dat";
<<"MRKansatz.dat";
<<"EMRK_limits_irreducible_functions.dat";
<<"MRK_limits_irreducible_functions.dat";

SVHPLtermsWeight[w_]:=SVHPLtermsWeight[w]=Get["weight_"<>ToString[w]<>"_SVHPL_basis.dat"];
HPLbasis[w_]:=HPLbasis[w]=Prepend[Flatten[Table[HPL[word,var],{word,generateLyndonBasis[w,{0,1}]},{var,{z,zb}}]],1];
fullHPLbasis[weight_]:=fullHPLbasis[weight]=Sort[Select[DeleteDuplicates[Flatten[Table[Times@@@Tuples[HPLbasis[weight-w],w],{w,weight-1}]]],transcendentalWeight[#]<weight&],transcendentalWeight[#1]>transcendentalWeight[#2]&];
irreducibleFunctionsToEMRK[limit_] := {H3[a_] :> EMRK[H3[a],limit], H4[a_] :> EMRK[H4[a],limit], H5[a_] :> EMRK[H5[a],limit], H6[a_] :> EMRK[H6[a],limit], H7[a_] :> EMRK[H7[a],limit], H8[a_] :> EMRK[H8[a],limit], H9[a_] :> EMRK[H9[a],limit], H10[a_] :> EMRK[H10[a],limit], Subscript[OverTilde[\[CapitalPhi]],6]:>EMRK[Subscript[OverTilde[\[CapitalPhi]],6],limit], Superscript[\[CapitalOmega], "(2)"][a_,b_,c_]:> EMRK[Superscript[\[CapitalOmega], "(2)"][a,b,c],limit], Subscript[F, 1][s_,b_,c_]:>EMRK[Subscript[F, 1][s,b,c],limit],Subscript[H, 1][s_,b_,c_]:>EMRK[Subscript[H, 1][s,b,c],limit], Subscript[J, 1][s_,b_,c_]:>EMRK[Subscript[J, 1][s,b,c],limit],N :>EMRK[N,limit], O :> EMRK[O,limit],  Subscript[M, 1][s_,b_,c_]:>EMRK[Subscript[M, 1][s,b,c],limit], Subscript[Q, "ep"][a_, b_, c_] :> EMRK[Subscript[Q, "ep"][a, b, c],limit], G :> EMRK[G,limit], Subscript[K, 1][a_, b_, c_]:>EMRK[Subscript[K, 1][a, b, c],limit]};
irreducibleFunctionsToMRK[limit_] := {H3[a_] :> MRK[H3[a],limit], H4[a_] :> MRK[H4[a],limit], H5[a_] :> MRK[H5[a],limit], H6[a_] :> MRK[H6[a],limit], H7[a_] :> MRK[H7[a],limit], H8[a_] :> MRK[H8[a],limit], H9[a_] :> MRK[H9[a],limit], H10[a_] :> MRK[H10[a],limit], Subscript[OverTilde[\[CapitalPhi]],6]:>MRK[Subscript[OverTilde[\[CapitalPhi]],6],limit], Superscript[\[CapitalOmega], "(2)"][a_,b_,c_]:> MRK[Superscript[\[CapitalOmega], "(2)"][a,b,c],limit], Subscript[F, 1][s_,b_,c_]:>MRK[Subscript[F, 1][s,b,c],limit],Subscript[H, 1][s_,b_,c_]:>MRK[Subscript[H, 1][s,b,c],limit], Subscript[J, 1][s_,b_,c_]:>MRK[Subscript[J, 1][s,b,c],limit],N :>MRK[N,limit], O :> MRK[O,limit],  Subscript[M, 1][s_,b_,c_]:>MRK[Subscript[M, 1][s,b,c],limit], Subscript[Q, "ep"][a_, b_, c_] :> MRK[Subscript[Q, "ep"][a, b, c],limit], G :> MRK[G,limit], Subscript[K, 1][a_, b_, c_]:>MRK[Subscript[K, 1][a, b, c],limit]};
toEMRKlimit[func_,varTo1_->1]:=Module[{u1=varTo1,u2=varTo1/.cycle,u3=varTo1/.cycle/.cycle},Expand[func/.irreducibleFunctionsToEMRK[u1->1]/.SVHPLreplacements/.{Subscript[z,u1]->z,Subscript[zb,u1]->zb}/.{Log[Subscript[\[Xi],u1]]:>HPL[{0},\[Xi]]}/.toHPL/.{u1->1-\[Xi]}/.flipArgument[{1-u2,1-u3,1-\[Xi]}]/.HPL[{___,1},Alternatives[\[Xi],u2,u3]]->0/.{HPL[{0},\[Xi]]->Log[\[Xi]], HPL[{0},u2]->Log[\[Xi]]+HPL[{1},z]+HPL[{1},zb], HPL[{0},u3]->Log[\[Xi]]+HPL[{0},z]+HPL[{0},zb]+HPL[{1},z]+HPL[{1},zb]}]];
toMRKlimit[func_,varTo1_->1]:=Module[{u1=varTo1,u2=varTo1/.cycle,u3=varTo1/.cycle/.cycle},Expand[func/.irreducibleFunctionsToMRK[u1->1]/.SVHPLreplacements/.{Subscript[z,u1]->z,Subscript[zb,u1]->zb}/.{Log[Subscript[\[Xi],u1]]:>HPL[{0},\[Xi]]}/.toHPL/.{\[Xi]->1-u1}/.flipArgument[{1-u2,1-u3,1-u1}]/.{HPL[{0},u1]->HPL[{0},u1]-2Pi I}/.flipArgument[u1]/.{u1->1-\[Xi]}/.{HPL[{___,1},\[Xi]]->0,HPL[{___,1},u2]->0,HPL[{___,1},u3]->0}/.{HPL[{0},\[Xi]]->Log[\[Xi]], HPL[{0},u2]->Log[\[Xi]]+HPL[{1},z]+HPL[{1},zb], HPL[{0},u3]->Log[\[Xi]]+HPL[{0},z]+HPL[{0},zb]+HPL[{1},z]+HPL[{1},zb]}]]/;func =!= 0;
toMRKlimit[0,varTo1_->1]:=0;

initializeEMRKsolver[weight_]:=Monitor[
	EMRKsolverCurrentWeight=-1;
	EMRKcoefficients=Flatten@Table[Table[c[w,i],{i,w+1}],{w,weight}];
	EMRKbackToSVHPL=Module[{termsWeight},termsWeight[w_]:=termsWeight[w]=DeleteDuplicates[Times@@@Tuples[{SVHPL[0],SVHPL[1]},w]]; EMRKcoefficients/.{c[w_,i_]:>termsWeight[w][[i]]}];
	EMRKansatz=Sum[EMRKansatzWeight[i],{i,weight}];
	EMRKdirections=Flatten@Table[i j,{i,Select[fullHPLbasis[weight],FreeQ[#,HPL[{__,1},_]]&]},{j,{1/z,1/(1-z)}}];
	EMRKtoVector=Table[EMRKdirections[[i]]->IdentityMatrix[Length[EMRKdirections]][[i]],{i,Length[EMRKdirections]}];
	EMRKvectors=Table[Expand[EMRKansatz/.flipArgument[{1-z,1-zb}]]/.EMRKcoefficients[[i]]->1/.Alternatives@@Drop[EMRKcoefficients,{i}]->0/.EMRKtoVector,{i,Length@EMRKcoefficients}];
	EMRKbasisMatrix=SparseArray[EMRKvectors\[Transpose]];
	EMRKsolverCurrentWeight=weight;,"Inializing weight "<>ToString[weight]<>" EMRK solver"];

initializeMRKsolver[weight_]:=Monitor[
	MRKsolverCurrentWeight=-1;
	MRKcoefficients=Flatten@Table[Table[c[w,i],{i,Length[SVHPLtermsWeight[w]]}],{w,weight}];
	MRKbackToSVHPL=MRKcoefficients/.{c[w_,i_]:>SVHPLtermsWeight[w][[i]]};
	MRKansatz=Sum[MRKansatzWeight[i],{i,weight}];
	MRKdirections=Flatten@Table[i j,{i,fullHPLbasis[weight]},{j,{1/z,1/(1-z)}}];
	MRKtoVector=Table[MRKdirections[[i]]->IdentityMatrix[Length[MRKdirections]][[i]],{i,Length[MRKdirections]}];
	MRKvectors=Table[Expand[MRKansatz/.flipArgument[{1-z,1-zb}]]/.MRKcoefficients[[i]]->1/.Alternatives@@Drop[MRKcoefficients,{i}]->0/.MRKtoVector,{i,Length@MRKcoefficients}];
	MRKbasisMatrix=SparseArray[MRKvectors\[Transpose]];
	MRKsolverCurrentWeight=weight;,"Inializing weight "<>ToString[weight]<>" MRK solver"];

toEMRK[func_,limit_:(u->1)]:= Module[{weight,zDiffInEMRKlimit,zSolutionFunc,zLimitMatching,EMRKfunc,u1=limit/.Rule[x_,_]:>x,u2=limit/.Rule[x_,_]:>x/.cycle,u3=limit/.Rule[x_,_]:>x/.cycle/.cycle},
	weight=transcendentalWeight[func];
	If[EMRKsolverCurrentWeight=!=weight,initializeEMRKsolver[weight]];
	zDiffInEMRKlimit=toEMRKlimit[coproductD[func,Subscript[z,u1]],limit];
	zSolutionFunc=If[zDiffInEMRKlimit=!=0,Expand[LinearSolve[EMRKbasisMatrix,zDiffInEMRKlimit/.EMRKtoVector].EMRKbackToSVHPL],0];
	zLimitMatching=Expand[ReplaceAll[toPointE[func,Which[u2===u,{u,u,1},u2===v,{1,v,v},u2===w,{w,1,w}],u2->0]/.toLogs,Log[u2]->Log[\[Xi]]-HPL[{0},1-z]-HPL[{0},1-zb]]-ReplaceAll[zSolutionFunc/.SVHPLreplacements/.flipArgument[{z,zb}],HPL[{___,1},1-Alternatives[z,zb]]->0]];
	EMRKfunc=Expand[Expand[zSolutionFunc+zLimitMatching]/.{SVHPL[x__]:>Subscript[SVHPL,u1][x],Log[\[Xi]]->Log[Subscript[\[Xi],u1]]}/.{Pi^3->6 Pi \[Zeta][2],Pi^5->90 Pi \[Zeta][4]}];
	checkEMRK\[Xi]D[func,EMRKfunc,limit];
	EMRKfunc];

toMRK[func_,limit_:(u->1)]:= Module[{weight,zDiffInMRKlimit,zSolutionFunc,zLimitMatching,MRKfunc,u1=limit/.Rule[x_,_]:>x,u2=limit/.Rule[x_,_]:>x/.cycle,u3=limit/.Rule[x_,_]:>x/.cycle/.cycle},
	weight=transcendentalWeight[func];
	If[MRKsolverCurrentWeight=!=weight,initializeMRKsolver[weight]];
	zDiffInMRKlimit=toMRKlimit[coproductD[func,Subscript[z,u1]],limit];
	zSolutionFunc=If[zDiffInMRKlimit=!=0,Expand[LinearSolve[MRKbasisMatrix,zDiffInMRKlimit/.MRKtoVector].MRKbackToSVHPL],0];
	zLimitMatching=Expand[ReplaceAll[toPointM[func,Which[u2===u,{u,u,1},u2===v,{1,v,v},u2===w,{w,1,w}],u2->0]/.toLogs,Log[u2]->Log[\[Xi]]-HPL[{0},1-z]-HPL[{0},1-zb]]-ReplaceAll[zSolutionFunc/.SVHPLreplacements/.flipArgument[{z,zb}],{HPL[{___,1},1-z]->0,HPL[{___,1},1-zb]->0}]];
	MRKfunc=Expand[Expand[zSolutionFunc+zLimitMatching]/.{SVHPL[a__]:>Subscript[SVHPL,u1][a],Log[\[Xi]]->Log[Subscript[\[Xi],u1]]}/.{Pi^3->6 Pi \[Zeta][2],Pi^5->90 Pi \[Zeta][4]}];
	checkMRK\[Xi]D[func,MRKfunc,limit];
	MRKfunc];

checkEMRK\[Xi]D[funcCoproduct_,funcEMRK_,1->varTo1_]:=Module[{coproductRepresentationD,EMRKrepresentationD,u1=varTo1,u2=varTo1/.cycle,u3=varTo1/.cycle/.cycle},
	coproductRepresentationD=Expand[coproductD[funcCoproduct,Subscript[\[Xi],u1]]/.irreducibleFunctionsToEMRK[1->u1]/.SVHPLreplacements/.toHPL/.{u1->1-Subscript[\[Xi],u1]}/.flipArgument[{1-Subscript[\[Xi],u1],1-u2,1-u3}]/.{HPL[{___,1},Alternatives[Subscript[\[Xi],u1],u2,u3]]->0,HPL[{0},Subscript[\[Xi],u1]]->Log[Subscript[\[Xi],u1]]}/.{HPL[{0},u2]->Log[Subscript[\[Xi],u1]]+HPL[{1},Subscript[z,u1]]+HPL[{1},Subscript[zb,u1]]}/.{HPL[{0},u3]->Log[Subscript[\[Xi],u1]]+HPL[{1},Subscript[z,u1]]+HPL[{1},Subscript[zb,u1]]+HPL[{0},Subscript[z,u1]]+HPL[{0},Subscript[zb,u1]]}/.\[Zeta][x_]:>Zeta[x]];
	EMRKrepresentationD=Expand[D[funcEMRK/.SVHPLreplacements,Subscript[\[Xi],u1]]/.\[Zeta][x_]:>Zeta[x]];
	If[Simplify[Expand[coproductRepresentationD-EMRKrepresentationD]]=!=0, Print["\[Xi] derivative of ",func," in EMRK representation does not match"]]];

checkMRK\[Xi]D[funcCoproduct_,funcMRK_,1->varTo1_]:=Module[{coproductRepresentationD,MRKrepresentationD,u1=varTo1,u2=varTo1/.cycle,u3=varTo1/.cycle/.cycle},
	coproductRepresentationD=Expand[coproductD[funcCoproduct,Subscript[\[Xi],u1]]/.irreducibleFunctionsToMRK[1->u1]/.SVHPLreplacements/.toHPL/.{Alternatives[\[Xi],Subscript[\[Xi],u1]]->1-u1}/.flipArgument[{1-u1,1-u2,1-u3}]/.HPL[{0},u1]->(HPL[{0},u1]-2*Pi*I)/.{u1->1-Subscript[\[Xi],u1]}/.flipArgument[1-Subscript[\[Xi],u1]]/.{HPL[{___,1},Alternatives[Subscript[\[Xi],u1],u2,u3]]->0,HPL[{0},Subscript[\[Xi],u1]]->Log[Subscript[\[Xi],u1]]}/.{HPL[{0},u2]->Log[Subscript[\[Xi],u1]]+HPL[{1},Subscript[z,u1]]+HPL[{1},Subscript[zb,u1]]}/.{HPL[{0},u3]->Log[Subscript[\[Xi],u1]]+HPL[{1},Subscript[z,u1]]+HPL[{1},Subscript[zb,u1]]+HPL[{0},Subscript[z,u1]]+HPL[{0},Subscript[zb,u1]]}/.\[Zeta][x_]:>Zeta[x]];
	MRKrepresentationD=Expand[D[funcMRK/.SVHPLreplacements,Subscript[\[Xi],u1]]/.\[Zeta][x_]:>Zeta[x]];
	If[Simplify[Expand[coproductRepresentationD-MRKrepresentationD]]=!=0, Print["\[Xi] derivative of ",func," in MRK representation does not match"]]];
