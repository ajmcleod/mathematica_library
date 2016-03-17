(* ::Package:: *)

If[$OperatingSystem=="Unix",$MathematicaLibrary="~/Mathematica/Mathematica Library"];
If[!ValueQ[stayInLyndonBasis],stayInLyndonBasis=True];
Do[Evaluate[Symbol["toSingularArgN"<>ToString[jj]<>"Ew"<>ToString[ii]<>"HPL"][x_, \[Delta]_]]={},{ii,5,10},{jj,2,3}];
SVHPLreplacements=irreducibleFunctionsToLineE[x_]=irreducibleDoubleScalingFunctionsToLineE[x_]={};

Get["irrToG.m"];
Get["coproductDifferentiation.m"];
Get["coproductIntegration.m"];
Get["functionConversions.m"];
Get[$MathematicaLibrary<>"/Function Library/Base Code/yGrading.m"];
Get[$MathematicaLibrary<>"/Function Library/Base Code/irreducible_function_coproducts.m"];
Get[$MathematicaLibrary<>"/Function Library/Base Code/irreducible_function_orbital_notation.m"];
Get[$MathematicaLibrary<>"/Function Library/Base Code/Local Binaries/transcendental_weight_"<>ToString[Floor[$VersionNumber]]<>".mx"];
Get[$MathematicaLibrary<>"/Function Library/Base Code/Local Binaries/irreducibleFunctionCoproduct_"<>ToString[Floor[$VersionNumber]]<>".mx"];
Get[$MathematicaLibrary<>"/Function Library/Base Code/functionLists.m"];
Get[$MathematicaLibrary<>"/Function Library/MZV/MZV.m"];
Get[$MathematicaLibrary<>"/Function Library/Identities/LyndRed/Lyndon.m"];
Get[$MathematicaLibrary<>"/Function Library/Basis Conversions/basisConversion.m"];
Get[$MathematicaLibrary<>"/Function Library/Identities/flipArgument/flipArgument.m"];
Get[$MathematicaLibrary<>"/Function Library/Identities/invertArgument/invertArgument.m"];
Get[$MathematicaLibrary<>"/Function Library/Identities/toSingularArgP/toSingularArgP.m"];
Get[$MathematicaLibrary<>"/Function Library/DS Limits/DS_limits.m"];
Get[$MathematicaLibrary<>"/Function Library/DT Limits/DT_limits.m"];
Get[$MathematicaLibrary<>"/Function Library/SP Limits/SP_limits.m"];
Get[$MathematicaLibrary<>"/Function Library/Hexagon Limits/uvwLimits.m"];
Get[$MathematicaLibrary<>"/Function Library/Six Points/MHV6.m"];
Get[$MathematicaLibrary<>"/Function Library/Six Points/NMHV6.m"];
Get[$MathematicaLibrary<>"/Function Library/Seven Points/heptagon.m"];
Get[$MathematicaLibrary<>"/Function Library/Identities/Canonical Integration Limits/Local Binaries/canonical_integration_limits_"<>ToString[Floor[$VersionNumber]]<>".mx"];

coproduct[weight_:Null,func_]:=toStrictLyndonBasis[coproductMaster[weight,Expand[func/.\[Pi]to\[Zeta]/.\[Pi]->\[Zeta][0,1,0]/.SVHPLreplacements/.toIMPL]]/.\[Zeta][0,1,0]->\[Pi]/.If[FreeQ[func,G[__]],IMPLtoHPL,IMPLtoG]]/;TrueQ[stayInLyndonBasis]\[And]Last[weight]!=1;
coproduct[weight_:Null,func_]:=ReplaceAll[toStrictLyndonBasis[coproductMaster[weight,Expand[func/.\[Pi]to\[Zeta]/.\[Pi]->\[Zeta][0,1,0]/.SVHPLreplacements/.toIMPL]]/.\[Zeta][0,1,0]->\[Pi]/.If[FreeQ[func,G[__]],IMPLtoHPL,IMPLtoG]],CircleDot[a__,b_]:>CircleDot[a,b/.toLogs]]/;TrueQ[stayInLyndonBasis]\[And]Last[weight]==1;
coproduct[weight_:Null,func_]:=(coproductMaster[weight,Expand[func/.\[Pi]to\[Zeta]/.\[Pi]->\[Zeta][0,1,0]/.SVHPLreplacements/.toIMPL]]/.\[Zeta][0,1,0]->\[Pi]/.If[FreeQ[func,G[__]],IMPLtoHPL,IMPLtoG])/;!TrueQ[stayInLyndonBasis]\[And]Last[weight]!=1;
coproduct[weight_:Null,func_]:=ReplaceAll[coproductMaster[weight,Expand[func/.\[Pi]to\[Zeta]/.\[Pi]->\[Zeta][0,1,0]/.SVHPLreplacements/.toIMPL]]/.\[Zeta][0,1,0]->\[Pi]/.If[FreeQ[func,G[__]],IMPLtoHPL,IMPLtoG],CircleDot[a__,b_]:>CircleDot[a,b/.toLogs]]/;!TrueQ[stayInLyndonBasis]\[And]Last[weight]==1;

coproductMaster[weight_,0]:=0;
coproductMaster[weights_,Plus[x_,y__]]:=Sum[coproductMaster[weights,i],{i,List[x,y]}];
coproductMaster[weights_,c_*Plus[x_,y__]]:=c*Sum[coproductMaster[weights,i],{i,List[x,y]}]/;NumericQ[c]\[And]FreeQ[c,Pi];
coproductMaster[weights_,Times[-1,func__]]:=-coproductMaster[weights,Times[func]];
coproductMaster[weights_,func_]:=Expand[If[MemberQ[{func},\[Zeta][__],Infinity],zetaValueCoproduct[weights,func],
									If[MemberQ[{func},Alternatives@@allIrreducibleFunctions,Infinity],irreducibleFunctionCoproduct[weights,func],
										If[weights===Null,fullCoproduct[func,CircleDot],
											If[weights===max,maxCoproduct[func],
												If[Length[weights]==2,twoCoproduct[weights,func,CircleDot],
													If[Length[weights]>2,higherCoproduct[weights,func,CircleDot]]]]]]]]/;!MatchQ[func,Alternatives[Times[-1,__],Plus[_,__]]]\[And]FreeQ[func,CircleDot];

twoCoproduct[weights_,0,outputType_]:=0;
twoCoproduct[weights_,c_*func_,outputType_]:=c*twoCoproduct[weights,func,outputType]/;NumericQ[c]\[And]FreeQ[c,Pi]\[And]!NumericQ[func];
twoCoproduct[weights_,IMPL[ai_,aVector_,af_],ouputType_]:=Print[StringJoin["The coproduct weights ",ToString[weights]," don't match the transcendental weight of the function ",ToString[IMPL[ai,aVector,af]]]]/;Length[aVector]!=Total[weights];
twoCoproduct[{0,w_},IMPL[ai_,aVector_,af_],outputType_]:=outputType[1,IMPL[ai,aVector,af]]/;w!=0;
twoCoproduct[{w_,0},IMPL[ai_,aVector_,af_],outputType_]:=outputType[IMPL[ai,aVector,af],1]/;w!=0;
twoCoproduct[weights_,Power[IMPL[0,aVector_,af_],n_],outputType_]:=Module[{dummyVars=Table[Unique[d],{i,n}]}, twoCoproduct[weights,Product[IMPL[0,aVector,dummyVars[[i]]],{i,n}],outputType]/.Table[dummyVars[[i]]->af,{i,n}]];
twoCoproduct[weights_,Times[x___,Power[IMPL[0,aVector_,af_],n_],y___],outputType_]:=Module[{dummyVars=Table[Unique[d],{i,n}]}, twoCoproduct[weights,Times@@Join[Table[IMPL[0,aVector,dummyVars[[i]]],{i,n}],{x,y}],outputType]/.Table[dummyVars[[i]]->af,{i,n}]];
twoCoproduct[weights_,Times[x___,IMPL[0,aVector_,Power[af_,n_]],y___],outputType_]:=Module[{tempVar},twoCoproduct[weights,Times[x,IMPL[0,aVector,tempVar],y],outputType]/.{tempVar->Power[af,n]}];
twoCoproduct[weights_,Times[x___,IMPL[0,{a1___,Power[a2_,n_],a3___},af_],y___],outputType_]:=Module[{tempVar},twoCoproduct[weights,Times[x,IMPL[0,{a1,tempVar,a3},af],y],outputType]/.{tempVar->Power[a2,n]}];
twoCoproduct[weights_,IMPL[ai_,aVector_,af_],ouputType_]:=Module[{vars=sumOverTwo[weights]},
	Sum[ouputType[IMPL[ai,Table[aVector[[vars[[i,j]]]],{j,Length[vars[[i]]]}],af],If[First[vars[[i]]]>1,IMPL[ai,Table[aVector[[l]],{l,First[vars[[i]]]-1}],aVector[[First[vars[[i]]]]]],1]Product[If[vars[[i,p]]<vars[[i,p+1]]-1,IMPL[aVector[[vars[[i,p]]]],Table[aVector[[l]],{l,vars[[i,p]]+1,vars[[i,p+1]]-1}],aVector[[vars[[i,p+1]]]]],1],{p,Length[vars[[i]]]-1}]If[Last[vars[[i]]]<Length[aVector],IMPL[aVector[[Last[vars[[i]]]]],Table[aVector[[l]],{l,Last[vars[[i]]]+1,Length[aVector]}],af],1]],{i,Length@vars}]]/;!MemberQ[weights,0];
twoCoproduct[weights_,Times[x_,y__],outputType_]:=Block[{functions=List[x,y],functionWeights,partitions,combinedCoproduct,b},
	functionWeights=ReplaceAll[functions,IMPL[ai_,aVector_,af_]:>Length[aVector]];
    partitions=Select[Flatten[Table[Array[b,Length@functions],##]&@@Table[{b[i],Max[0,Last@weights-Total[Drop[functionWeights,{i}]]],Min[functionWeights[[i]],Last@weights]},{i,Length@functions}],Length@functions-1],Total[#]==Last[weights]&];	
	combinedCoproduct[remainingFunctionWeights_,remainingPartitionWeights_,remainingFunctions_]:=coproductTimes[combinedCoproduct[Drop[remainingFunctionWeights,-1],Drop[remainingPartitionWeights,-1],Drop[remainingFunctions,-1]],twoCoproduct[{Last[remainingFunctionWeights]-Last[remainingPartitionWeights],Last[remainingPartitionWeights]},Last[remainingFunctions],outputType]]/;Length@remainingFunctions>2;
	combinedCoproduct[remainingFunctionWeights_,remainingPartitionWeights_,remainingFunctions_]:=coproductTimes[twoCoproduct[{First[remainingFunctionWeights]-First[remainingPartitionWeights],First[remainingPartitionWeights]},First[remainingFunctions],outputType],twoCoproduct[{Last[remainingFunctionWeights]-Last[remainingPartitionWeights],Last[remainingPartitionWeights]},Last[remainingFunctions],outputType]]/;Length@remainingFunctions==2;
	If[Total[weights]==Total[functionWeights],Sum[combinedCoproduct[functionWeights,partitions[[i]],functions],{i,Length@partitions}]//.{outputType[f1_,f2_]:>outputType[f1,f2]},Print[StringJoin["The coproduct weights ",ToString[weights]," don't match the transcendental weight of the function ",ToString[Times[x,y]]]]]]/;FreeQ[List[x,y],Power,Infinity]\[And]Select[List[x,y],NumericQ[#]&]=={};

sumOverTwo[weights_]:=Module[{partitions=IntegerPartitions[Total[weights]+1],choose,allPermutations},
	choose=Select[partitions,Total[#]-Length[#]==Last@weights&];
	allPermutations=Join@@Table[Permutations[choose[[i]]],{i,Length@choose}];
	Table[Table[Total[Take[(allPermutations[[i]]),j]],{j,Length@allPermutations[[i]]-1}],{i,Length@allPermutations}]]

higherCoproduct[weights_,func_,outputType_]:=ReplaceAll[twoCoproduct[{Total[Drop[weights,-1]],Last[weights]},func,CircleDot],CircleDot[x_,y_]:>outputType[coproductMaster[Drop[weights,-1],x],y]];

maxCoproduct[func_]:=Module[{w=transcendentalWeight[func]}, If[w>1\[And]!MatchQ[func,pureMZV],coproductMaster[{Floor[w/2],Ceiling[w/2]},func]/.{CircleDot[x_,y_]:>CircleDot[coproductMaster[max,x],coproductMaster[max,y]]},func]]/;FreeQ[func,CircleDot[x__],Infinity];

fullCoproduct[Times[x_,y__],outputType_]:=coproductTimes[fullCoproduct[x,outputType],fullCoproduct[Times[y],outputType]];
fullCoproduct[Power[x_,n_]outputType_]:=coproductTimes[fullCoproduct[x,outputType],fullCoproduct[Power[x,n-1],outputType]];
fullCoproduct[IMPL[ai_,aVector_,af_],outputType_]:=Module[{kMax=Length@aVector,d},Sum[Sum[outputType[IMPL[ai,Table[aVector[[d[i]]],{i,k}],af],If[d[1]>1,IMPL[ai,Table[aVector[[l]],{l,d[1]-1}],aVector[[d[1]]]],1]Product[If[d[i]<d[i+1]-1,IMPL[aVector[[d[i]]],Table[aVector[[l]],{l,d[i]+1,d[i+1]-1}],aVector[[d[i+1]]]],1],{i,k-1}]If[d[k]<kMax,IMPL[aVector[[d[k]]],Table[aVector[[l]],{l,d[k]+1,kMax}],af],1]],##]&@@Join[{{d[1],kMax}},Table[{d[j],d[j-1]+1,kMax},{j,2,k}]],{k,kMax}]]+outputType[1,IMPL[ai,aVector,af]];

irreducibleFunctionCoproduct[weights_,Times[c_,funcN__]]:=c*irreducibleFunctionCoproduct[weights,Times[funcN]]/;NumericQ[c]\[And]FreeQ[c,Pi];
irreducibleFunctionCoproduct[{w__,1},func_]:=(irreducibleFunctionCoproduct[{transcendentalWeight[func]-1,1},func]/.{CircleDot[x_,y_]:>CircleDot[coproductMaster[{w},Expand[x/.\[Pi]to\[Zeta]/.\[Pi]->\[Zeta][0,1,0]/.SVHPLreplacements/.toIMPL]],Expand[y/.\[Pi]->0/.\[Zeta][__]->0/.SVHPLreplacements/.toIMPL]]})/;Length[List[w]]>1\[And]MemberQ[allIrreducibleFunctions,func];
irreducibleFunctionCoproduct[{w_,1},Times[func1_,funcN__]]:=Sum[coproductMaster[{transcendentalWeight[f]-1,1},f]/.{CircleDot[x_,y_]:>CircleDot[Expand[Times[Times@@DeleteCases[List[func1,funcN],f],x]/.\[Pi]to\[Zeta]/.\[Pi]->\[Zeta][0,1,0]/.SVHPLreplacements/.toIMPL],Expand[y/.\[Pi]->0/.\[Zeta][__]->0/.SVHPLreplacements/.toIMPL]]},{f,List[func1,funcN]}]/;Select[List[func1,funcN],NumericQ[#]&]=={};
irreducibleFunctionCoproduct[{w__,1},Times[func1_,funcN__]]:=Sum[coproductMaster[{transcendentalWeight[f]-1,1},f]/.{CircleDot[x_,y_]:>CircleDot[Expand[Times[Times@@DeleteCases[List[func1,funcN],f],x]/.\[Pi]to\[Zeta]/.\[Pi]->\[Zeta][0,1,0]/.SVHPLreplacements/.toIMPL],Expand[y/.\[Pi]->0/.\[Zeta][__]->0/.SVHPLreplacements/.toIMPL]]},{f,List[func1,funcN]}]/.CircleDot[term1_,term2__]:>CircleDot[coproductMaster[{w},term1],term2]/;Length[List[w]]>1\[And]Select[List[func1,funcN],NumericQ[#]&]=={};
irreducibleFunctionCoproduct[{w_,1},Power[func_,n_]]:=Expand[n*coproductMaster[{transcendentalWeight[func]-1,1},func]/.{CircleDot[x_,y_]:>CircleDot[Expand[x*Power[func,n-1]/.\[Pi]to\[Zeta]/.\[Pi]->\[Zeta][0,1,0]/.SVHPLreplacements/.toIMPL],y]}];
irreducibleFunctionCoproduct[{w__,1},Power[func_,n_]]:=Expand[n*coproductMaster[{transcendentalWeight[func]-1,1},func]/.{CircleDot[x_,y_]:>CircleDot[Expand[x*Power[func,n-1]/.\[Pi]to\[Zeta]/.\[Pi]->\[Zeta][0,1,0]/.SVHPLreplacements/.toIMPL],y]}]/.CircleDot[term1_,term2__]:>CircleDot[coproductMaster[{w},term1],term2];Length[List[w]]>1;
irreducibleFunctionCoproduct[max,Times[func1_,funcN__]]:=Sum[coproductMaster[{transcendentalWeight[f]-1,1},f]/.{CircleDot[x_,y_]:>CircleDot[coproductMaster[max,Expand[Times[Times@@DeleteCases[List[func1,funcN],f],x]/.\[Pi]to\[Zeta]/.\[Pi]->\[Zeta][0,1,0]/.SVHPLreplacements/.toIMPL]], Expand[y/.\[Pi]->0/.\[Zeta][__]->0/.SVHPLreplacements/.toIMPL]]},{f,List[func1,funcN]}]/;Select[List[func1,funcN],NumericQ[#]&]=={};
irreducibleFunctionCoproduct[max,func_]:=coproductMaster[{transcendentalWeight[func]-1,1},func]/.CircleDot[x_,y_]:>CircleDot[coproductMaster[max,Expand[x/.\[Pi]to\[Zeta]/.\[Pi]->\[Zeta][0,1,0]/.SVHPLreplacements/.toIMPL]],Expand[y/.\[Pi]->0/.\[Zeta][__]->0/.SVHPLreplacements/.toIMPL]];

zetaValueCoproduct[weights_,0]=0;
zetaValueCoproduct[weights_,c_*func_]:=c*zetaValueCoproduct[weights,func]/;NumericQ[c]\[And]FreeQ[c,Pi];
zetaValueCoproduct[max,x_]:=CircleDot[x]/;MatchQ[x,pureMZV];
zetaValueCoproduct[max,Times[func_,x_]]:=(coproductMaster[{transcendentalWeight[Times[func,x]]-1,1},Times[func,x]]/.{CircleDot[a_,b_]:>CircleDot[coproductMaster[max,a],b]})/;MatchQ[x,pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]MemberQ[{func},Alternatives@@allIrreducibleFunctions,Infinity];
zetaValueCoproduct[max,Times[func_,x_]]:=CircleDot[x,coproductMaster[max,func]]/;MatchQ[x,pureMZV]\[And]FreeQ[func,Alternatives@@Append[allIrreducibleFunctions,\[Zeta][__]]];
zetaValueCoproduct[weights_,x_]:=If[First[weights]==transcendentalWeight[x]\[And]DeleteCases[Drop[weights,1],0]=={},CircleDot[x],0]/;MatchQ[x,pureMZV]\[And]weights=!=Alternatives[Null,max];
zetaValueCoproduct[weights_,Times[func_,\[Zeta][n__]]]:=splitCoproduct[weights,func,\[Zeta][n]]/;MatchQ[Times[\[Zeta][n]],pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]weights=!=Alternatives[Null,max];
zetaValueCoproduct[weights_,Times[func_,\[Zeta][n1__]\[Zeta][n2__]]]:=splitCoproduct[weights,func,\[Zeta][n1]\[Zeta][n2]]/;MatchQ[Times[\[Zeta][n1]\[Zeta][n2]],pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]weights=!=Alternatives[Null,max];
zetaValueCoproduct[weights_,Times[func_,\[Zeta][n1__]\[Zeta][n2__]\[Zeta][n3__]]]:=splitCoproduct[weights,func,\[Zeta][n1]\[Zeta][n2]\[Zeta][n3]]/;MatchQ[Times[\[Zeta][n1]\[Zeta][n2]\[Zeta][n3]],pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]weights=!=Alternatives[Null,max];
zetaValueCoproduct[weights_,Times[func_,\[Zeta][n1__]\[Zeta][n2__]\[Zeta][n3__]\[Zeta][n4__]]]:=splitCoproduct[weights,func,\[Zeta][n1]\[Zeta][n2]\[Zeta][n3]\[Zeta][n4]]/;MatchQ[Times[\[Zeta][n1]\[Zeta][n2]\[Zeta][n3]],pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]weights=!=Alternatives[Null,max];
zetaValueCoproduct[weights_,Times[func_,Power[\[Zeta][n__],m_]]]:=splitCoproduct[weights,func,Power[\[Zeta][n],m]]/;MatchQ[Times[Power[\[Zeta][n],m]],pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]weights=!=Alternatives[Null,max];
zetaValueCoproduct[weights_,Times[func_,\[Zeta][n1__]Power[\[Zeta][n2__],m_]]]:=splitCoproduct[weights,func,\[Zeta][n1]Power[\[Zeta][n2],m]]/;MatchQ[Times[\[Zeta][n1]Power[\[Zeta][n2],m]],pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]weights=!=Alternatives[Null,max];
splitCoproduct[weights_,func_,pureConstant_]:=Module[{\[Zeta]weight=transcendentalWeight[pureConstant]},
	Which[\[Zeta]weight<First[weights], coproductMaster[Prepend[Drop[weights,1],First[weights]-\[Zeta]weight],func]/.{CircleDot[x_,y_]:>CircleDot[Times[pureConstant, x],y]},
			\[Zeta]weight==First[weights]\[And]Length[weights]==2\[And]Total[Drop[weights,1]]==transcendentalWeight[func], CircleDot[pureConstant,func],
			\[Zeta]weight==First[weights]\[And]Length[weights]>2, CircleDot[pureConstant,coproductMaster[Drop[weights,1],func]],
			\[Zeta]weight>First[weights],0,
			Total[weights]!=transcendentalWeight[func],Print[StringJoin["The coproduct weights ",ToString[weights]," don't match the transcendental weight of the function ",ToString[Times[pureConstant,func]]]]]];

CircleDot[y_,z__]:=CircleDot[Expand[y],z]/;!MatchQ[y,Expand[y]];
CircleDot[x__,y_]:=CircleDot[x,Expand[y]]/;!MatchQ[y,Expand[y]];
CircleDot[x__,y_,z__]:=CircleDot[x,Expand[y],z]/;!MatchQ[y,Expand[y]];
CircleDot[x___,y_,z___]:=Plus@@Table[CircleDot[x,y[[i]],z],{i,Length[y]}]/;MatchQ[y,Plus[_,__]];
CircleDot[x___,c_*y_,z___]:=c*CircleDot[x,y,z]/;NumericQ[c]\[And]FreeQ[c,Pi]\[And]!NumericQ[y];
CircleDot[x___,CircleDot[y__],z___]:=CircleDot[x,y,z];
CircleDot[x___,y1_*y2__,z___]:=y1*CircleDot[x,y2,z]/;NumberQ[y1];
CircleDot[x___,0,z___]:=0;
CircleDot[x__,\[Zeta][__],z___]:=0;
CircleDot[x__,\[Zeta][__]*y_,z___]:=0;
CircleDot[x___,HPL[{0},arg_],z___]:=CircleDot[x,Log[arg],z];
CircleDot[x___,HPL[{1},arg_],z___]:=-CircleDot[x,Log[1-arg],z];
CircleDot[x___,G[{0},arg_],z___]:=CircleDot[x,Log[arg],z];
CircleDot[x___,G[{1},arg_],z___]:=CircleDot[x,Log[1-arg],z];

coproductTimes[x_,y_]:=Plus@@Table[coproductTimes[x,y[[i]]],{i,Length[y]}]/;MatchQ[y,Plus[_,__]];
coproductTimes[x_,y_]:=Plus@@Table[coproductTimes[x[[i]],y],{i,Length[x]}]/;MatchQ[x,Plus[_,__]];
coproductTimes[c_*CircleDot[x__],y_]:=c*coproductTimes[CircleDot[x],y]/;NumericQ[c]\[And]FreeQ[c,Pi];
coproductTimes[x_,c_*CircleDot[y__]]:=c*coproductTimes[x,CircleDot[y]]/;NumericQ[c]\[And]FreeQ[c,Pi];
(*coproductTimes[x_,y_]:=-coproductTimes[x,-y]/;MatchQ[y,Times[-1,__]];*)
(*coproductTimes[fullCoproduct[c_],CircleDot[x__]]:=c*CircleDot[x]/;NumericQ[c]\[And]FreeQ[c,Pi];*) (*new!*)
coproductTimes[CircleDot[x1_,y1_],CircleDot[x2_,y2_]]:=CircleDot[x1 x2, y1 y2];
coproductTimes[x_,0]:=0;
coproductTimes[0,x_]:=0;

shuffle[func_]:=toHPLorG[shuffleIMPL[func/.toIMPL]];
shuffleG[func_]:=Expand[shuffleIMPL[func/.GtoIMPL]/.IMPLtoG];
shuffleHPL[func_]:=Expand[shuffleIMPL[func/.HPLtoIMPL]/.IMPLtoHPL];
shuffleIMPL[Plus[x_,y__]]:=Plus@@Table[shuffleIMPL[i],{i,List[x,y]}];
shuffleIMPL[Times[x___,IMPL[0,aVector_,f_],y___,IMPL[0,bVector_,f_],z___]]:=Module[{shuffles=shuffleW[aVector,bVector]},Sum[shuffleIMPL[Times[x,y,z,IMPL[0,shuffles[[i]],f]]],{i,Length@shuffles}]];
shuffleIMPL[Times[x___,IMPL[0,aVector_,f_],y___]]:=IMPL[0,aVector,f] shuffleIMPL[Times[x,y]]/;FreeQ[List[x,y],IMPL[0,_,f],Infinity];
shuffleIMPL[Power[IMPL[0,aVector_,f_],n_]]:=Module[{shuffles,l,j}, shuffles=shuffleW[aVector,aVector]; For[l=2,l<n,l++,shuffles=Join@@Table[shuffleW[aVector,shuffles[[j]]],{j,Length@shuffles}]]; Sum[IMPL[0,shuffles[[j]],f],{j,Length@shuffles}]];
shuffleIMPL[Times[x__,Power[IMPL[0,aVector_,f_],n_]]]:=Module[{shuffles,l,j}, shuffles=shuffleW[aVector,aVector]; For[l=2,l<n,l++,shuffles=Join@@Table[shuffleW[aVector,shuffles[[j]]],{j,Length@shuffles}]]; Sum[shuffleIMPL[Times[x,IMPL[0,shuffles[[j]],f]]],{j,Length@shuffles}]];
shuffleIMPL[c_ IMPL[0,aVector_,f_]]:=IMPL[0,aVector,f]/;NumericQ[c];
shuffleIMPL[IMPL[0,aVector_,f_]]:=IMPL[0,aVector,f];
shuffleIMPL[c_]:=c/;NumericQ[c];
shuffleIMPL[rational_]:=rational/;FreeQ[rational,IMPL[0,_,_]];
shuffleIMPL[\[Zeta][x__]]:=\[Zeta][x];
shuffleIMPL[\[Zeta][x__]^n_]:=\[Zeta][x]^n;
shuffleIMPL[\[Zeta][x__]func_]:=\[Zeta][x]shuffleIMPL[func];
shuffleIMPL[\[Zeta][x__]^n_*func_]:=\[Zeta][x]^n*shuffleIMPL[func];
shuffleW[s1_,s2_]:=Module[{p,tp,accf,ord}, p=Permutations@Join[1&/@s1,0&/@s2]; tp=BitXor[p,1]; accf=Accumulate[#\[Transpose]]\[Transpose] #&; ord=accf[p]+(accf[tp]+Length[s1]) tp; Outer[Part,{Join[s1,s2]},ord,1]//First];

toLinearBasis[Times[a_,x__]]:=a*toLinearBasis[Times[x]]/;NumericQ[a];
toLinearBasis[Plus[x_,y__]]:=Sum[toLinearBasis[i],{i,List[x,y]}];
toLinearBasis[Times[x__,Plus[y_,z__]]]:=toLinearBasis[Expand[Times[x,Plus[y,z]]]]/;!Or@@NumericQ/@List[x];
toLinearBasis[CircleDot[x__]]:=CircleDot@@Table[shuffle[List[x][[i]]],{i,Length@List[x]}];
toLinearBasis[func_]:=shuffle[func]/;!MatchQ[func,Alternatives[Times[x_,y__]/;NumericQ[x],Plus[_,__],CircleDot[__]]];
toLinearBasisHPL[Times[a_,x__]]:=a*toLinearBasisHPL[Times[x]]/;NumericQ[a];
toLinearBasisHPL[Plus[x_,y__]]:=Sum[toLinearBasisHPL[i],{i,List[x,y]}];
toLinearBasisHPL[Times[x__,Plus[y_,z__]]]:=toLinearBasisHPL[Expand[Times[x,Plus[y,z]]]]/;!Or@@NumericQ/@List[x];
toLinearBasisHPL[CircleDot[x__]]:=CircleDot@@Table[shuffleHPL[List[x][[i]]],{i,Length@List[x]}];
toLinearBasisHPL[func_]:=shuffleHPL[func]/;!MatchQ[func,Alternatives[Times[x_,y__]/;NumericQ[x],Plus[_,__],CircleDot[__]]];
toLinearBasisG[Times[a_,x__]]:=a*toLinearBasisG[Times[x]]/;NumericQ[a];
toLinearBasisG[Plus[x_,y__]]:=Sum[toLinearBasisG[i],{i,List[x,y]}];
toLinearBasisG[Times[x__,Plus[y_,z__]]]:=toLinearBasisG[Expand[Times[x,Plus[y,z]]]]/;!Or@@NumericQ/@List[x];
toLinearBasisG[CircleDot[x__]]:=CircleDot@@Table[shuffleG[List[x][[i]]],{i,Length@List[x]}];
toLinearBasisG[func_]:=shuffleG[func]/;!MatchQ[func,Alternatives[Times[x_,y__]/;NumericQ[x],Plus[_,__],CircleDot[__]]];
toLyndonBasis[func_]:=optimizeLyndonBasisReplacement[func];
toStrictLyndonBasis[func_]:=Expand[optimizeLyndonBasisReplacement[func]/.{G[aVec_,x_]:>Power[G[{First[aVec]},x],Length[aVec]]/(Length[aVec]!)/;Count[aVec,First[aVec]]==Length[aVec],HPL[aVec_,x_]:>Power[HPL[{First[aVec]},x],Length[aVec]]/(Length[aVec]!)/;Count[aVec,First[aVec]]==Length[aVec]}];

checkIntegrability[func_,max]:=Module[{maxCoproduct,checkEntries,weight=transcendentalWeight[func]},
	maxCoproduct=coproduct[max,func]/.toLogs/.\[Pi]to\[Zeta]/.{CircleDot[a_,b__]:>a checkIntegrability[CircleDot[b],max]/;MatchQ[a,pureMZV]\[And]Length[List[b]]>1,CircleDot[a_,b__]:>0/;MatchQ[a,pureMZV]\[And]Length[List[b]]==1};
	checkEntries[m_]:=maxCoproduct/.{CircleDot[a___,Log[b_],Log[c_],d___]:>SubMinus[CircleDot[a]]SubPlus[CircleDot[d]]AngleBracket[b,c]/;Length[List[a]]==m-1\[And]Length[List[d]]==weight-1-m};
	Sum[Expand[checkEntries[i]],{i,weight-1}]];
checkIntegrability[func_,last]:=Expand[func/.CircleDot[x_,y_]:>CircleDot[coproduct[{transcendentalWeight[func]-2,1},x],y]/.CircleDot[a__,b_,c_]:>CircleDot[a,b/.toLogs,c/.toLogs]/.\[Pi]to\[Zeta]/.{CircleDot[a___,Log[b_],Log[c_]]:>CircleDot[a]AngleBracket[b,c]}/.toHPL/.flipArgument[{u,v,w}]/.CircleDot[a__]:>toLinearBasis[CircleDot[a]]];

yReplacements={yu->-((-1-u+v+w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])/(1+u-v-w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])),yv->-((-1+u-v+w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])/(1-u+v-w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])),yw->-((-1+u+v-w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])/(1-u-v+w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])), y11 -> (1 - u4 - u5 + u1*u4*u5 - u3*u6 + Sqrt[\[CapitalDelta]1])/(1 - u4 - u5 + u1*u4*u5 - u3*u6 - Sqrt[\[CapitalDelta]1]), y12 -> (1 - u5 - u6 + u2*u5*u6 - u4*u7 + Sqrt[\[CapitalDelta]2])/(1 - u5 - u6 + u2*u5*u6 - u4*u7 - Sqrt[\[CapitalDelta]2]), y13 -> (-1 + u1*u5 + u6 + u7 - u3*u6*u7 - Sqrt[\[CapitalDelta]3])/(-1 + u1*u5 + u6 + u7 - u3*u6*u7 + Sqrt[\[CapitalDelta]3]), y14 -> (1 - u1 - u2*u6 - u7 + u1*u4*u7 + Sqrt[\[CapitalDelta]4])/(1 - u1 - u2*u6 - u7 + u1*u4*u7 - Sqrt[\[CapitalDelta]4]), y15 -> (1 - u1 - u2 + u1*u2*u5 - u3*u7 + Sqrt[\[CapitalDelta]5])/(1 - u1 - u2 + u1*u2*u5 - u3*u7 - Sqrt[\[CapitalDelta]5]), y16 -> (1 - u2 - u3 - u1*u4 + u2*u3*u6 + Sqrt[\[CapitalDelta]6])/(1 - u2 - u3 - u1*u4 + u2*u3*u6 - Sqrt[\[CapitalDelta]6]), y17 -> (1 - u3 - u4 - u2*u5 + u3*u4*u7 + Sqrt[\[CapitalDelta]7])/(1 - u3 - u4 - u2*u5 + u3*u4*u7 - Sqrt[\[CapitalDelta]7]), y21 -> ((1 - u5 - u6 + u2*u5*u6 - u4*u7 + 2*u4*u6*u7 - Sqrt[\[CapitalDelta]2])*(1 - u2 - u3 - u1*u4 + u2*u3*u6 + Sqrt[\[CapitalDelta]6]))/((1 - u5 - u6 + u2*u5*u6 - u4*u7 + 2*u4*u6*u7 + Sqrt[\[CapitalDelta]2])*(1 - u2 - u3 - u1*u4 + u2*u3*u6 - Sqrt[\[CapitalDelta]6])), y22 -> ((1 - u1*u5 - u6 - u7 + 2*u1*u5*u7 + u3*u6*u7 - Sqrt[\[CapitalDelta]3])*(1 - u3 - u4 - u2*u5 + u3*u4*u7 + Sqrt[\[CapitalDelta]7]))/((1 - u1*u5 - u6 - u7 + 2*u1*u5*u7 + u3*u6*u7 + Sqrt[\[CapitalDelta]3])*(1 - u3 - u4 - u2*u5 + u3*u4*u7 - Sqrt[\[CapitalDelta]7])), y23 -> ((1 - u4 - u5 + u1*u4*u5 - u3*u6 + Sqrt[\[CapitalDelta]1])*(1 - u1 - u2*u6 + 2*u1*u2*u6 - u7 + u1*u4*u7 - Sqrt[\[CapitalDelta]4]))/((1 - u4 - u5 + u1*u4*u5 - u3*u6 - Sqrt[\[CapitalDelta]1])*(1 - u1 - u2*u6 + 2*u1*u2*u6 - u7 + u1*u4*u7 + Sqrt[\[CapitalDelta]4])), y24 -> ((1 - u5 - u6 + u2*u5*u6 - u4*u7 + Sqrt[\[CapitalDelta]2])*(1 - u1 - u2 + u1*u2*u5 - u3*u7 + 2*u2*u3*u7 - Sqrt[\[CapitalDelta]5]))/((1 - u5 - u6 + u2*u5*u6 - u4*u7 - Sqrt[\[CapitalDelta]2])*(1 - u1 - u2 + u1*u2*u5 - u3*u7 + 2*u2*u3*u7 + Sqrt[\[CapitalDelta]5])), y25 -> ((-1 + u1*u5 + u6 + u7 - u3*u6*u7 - Sqrt[\[CapitalDelta]3])*(1 - u2 - u3 - u1*u4 + 2*u1*u3*u4 + u2*u3*u6 - Sqrt[\[CapitalDelta]6]))/((-1 + u1*u5 + u6 + u7 - u3*u6*u7 + Sqrt[\[CapitalDelta]3])*(1 - u2 - u3 - u1*u4 + 2*u1*u3*u4 + u2*u3*u6 + Sqrt[\[CapitalDelta]6])), y26 -> ((1 - u1 - u2*u6 - u7 + u1*u4*u7 + Sqrt[\[CapitalDelta]4])*(1 - u3 - u4 - u2*u5 + 2*u2*u4*u5 + u3*u4*u7 - Sqrt[\[CapitalDelta]7]))/((1 - u1 - u2*u6 - u7 + u1*u4*u7 - Sqrt[\[CapitalDelta]4])*(1 - u3 - u4 - u2*u5 + 2*u2*u4*u5 + u3*u4*u7 + Sqrt[\[CapitalDelta]7])), y27 -> ((1 - u4 - u5 + u1*u4*u5 - u3*u6 + 2*u3*u5*u6 - Sqrt[\[CapitalDelta]1])*(1 - u1 - u2 + u1*u2*u5 - u3*u7 + Sqrt[\[CapitalDelta]5]))/((1 - u4 - u5 + u1*u4*u5 - u3*u6 + 2*u3*u5*u6 + Sqrt[\[CapitalDelta]1])*(1 - u1 - u2 + u1*u2*u5 - u3*u7 - Sqrt[\[CapitalDelta]5]))};
replace\[CapitalDelta]={\[CapitalDelta]->(1-u-v-w)^2-4u v w, \[CapitalDelta]1 -> 1 - 2*u4 + u4^2 - 2*u5 + 2*u4*u5 + 2*u1*u4*u5 - 2*u1*u4^2*u5 + u5^2 - 2*u1*u4*u5^2 + u1^2*u4^2*u5^2 - 2*u3*u6 + 2*u3*u4*u6 + 2*u3*u5*u6 - 4*u3*u4*u5*u6 + 2*u1*u3*u4*u5*u6 + u3^2*u6^2,  \[CapitalDelta]2 -> 1 - 2*u5 + u5^2 - 2*u6 + 2*u5*u6 + 2*u2*u5*u6 - 2*u2*u5^2*u6 + u6^2 - 2*u2*u5*u6^2 + u2^2*u5^2*u6^2 - 2*u4*u7 + 2*u4*u5*u7 + 2*u4*u6*u7 - 4*u4*u5*u6*u7 + 2*u2*u4*u5*u6*u7 + u4^2*u7^2, \[CapitalDelta]3 -> 1 - 2*u1*u5 + u1^2*u5^2 - 2*u6 + 2*u1*u5*u6 + u6^2 - 2*u7 + 2*u1*u5*u7 + 2*u6*u7 + 2*u3*u6*u7 - 4*u1*u5*u6*u7 + 2*u1*u3*u5*u6*u7 - 2*u3*u6^2*u7 + u7^2 - 2*u3*u6*u7^2 + u3^2*u6^2*u7^2, \[CapitalDelta]4 -> 1 - 2*u1 + u1^2 - 2*u2*u6 + 2*u1*u2*u6 + u2^2*u6^2 - 2*u7 + 2*u1*u7 + 2*u1*u4*u7 - 2*u1^2*u4*u7 + 2*u2*u6*u7 - 4*u1*u2*u6*u7 + 2*u1*u2*u4*u6*u7 + u7^2 - 2*u1*u4*u7^2 + u1^2*u4^2*u7^2,  \[CapitalDelta]5 -> 1 - 2*u1 + u1^2 - 2*u2 + 2*u1*u2 + u2^2 + 2*u1*u2*u5 - 2*u1^2*u2*u5 - 2*u1*u2^2*u5 + u1^2*u2^2*u5^2 - 2*u3*u7 + 2*u1*u3*u7 + 2*u2*u3*u7 - 4*u1*u2*u3*u7 + 2*u1*u2*u3*u5*u7 + u3^2*u7^2, \[CapitalDelta]6 -> 1 - 2*u2 + u2^2 - 2*u3 + 2*u2*u3 + u3^2 - 2*u1*u4 + 2*u1*u2*u4 + 2*u1*u3*u4 - 4*u1*u2*u3*u4 + u1^2*u4^2 + 2*u2*u3*u6 - 2*u2^2*u3*u6 - 2*u2*u3^2*u6 + 2*u1*u2*u3*u4*u6 + u2^2*u3^2*u6^2, \[CapitalDelta]7 -> 1 - 2*u3 + u3^2 - 2*u4 + 2*u3*u4 + u4^2 - 2*u2*u5 + 2*u2*u3*u5 + 2*u2*u4*u5 - 4*u2*u3*u4*u5 + u2^2*u5^2 + 2*u3*u4*u7 - 2*u3^2*u4*u7 - 2*u3*u4^2*u7 + 2*u2*u3*u4*u5*u7 + u3^2*u4^2*u7^2};
uReplacements={1-u->(1-yu)(1-yu*yv*yw)/((1-yu*yv)(1-yu*yw)),1-v->(1-yv)(1-yu*yv*yw)/((1-yv yu)(1-yv*yw)),1-w->(1-yw)(1-yu*yv*yw)/((1-yw yu)(1-yw yv)),u->yu(1-yv)(1-yw)/((1-yu*yv)(1-yu*yw)),v->yv(1-yu)(1-yw)/((1-yv yu)(1-yv*yw)),w->yw(1-yu)(1-yv)/((1-yw yu)(1-yw yv))};
\[Xi]replacements={Subscript[\[Xi],u]->((1-yu)*(1-yu*yv*yw))/((1-yu*yv)*(1-yu*yw)),Subscript[\[Xi],v]->((1-yv)*(1-yu*yv*yw))/((1-yu*yv)*(1-yv*yw)),Subscript[\[Xi],w]->((1-yw)*(1-yu*yv*yw))/((1-yu*yw)*(1-yv*yw)),\[Xi]->((1-yu)*(1-yu*yv*yw))/((1-yu*yv)*(1-yu*yw))};
zLogReplacements = {Log[Subscript[z,u]]->Log[((1-yv)*(1-yu*yv)*yw)/(yv*(1-yw)*(1-yu*yw))]-Log[Subscript[zb,u]],Log[1-Subscript[z,u]]->Log[((1-yv*yw)*(1-yu*yv*yw))/(yv*(1-yw)*(1-yu*yw))]-Log[1-Subscript[zb,u]],Log[Subscript[z,v]]->Log[(yu*(1-yw)*(1-yv*yw))/((1-yu)*(1-yu*yv)*yw)]-Log[Subscript[zb,v]],Log[1-Subscript[z,v]]->Log[((1-yu*yw)*(1-yu*yv*yw))/((1-yu)*(1-yu*yv)*yw)]-Log[1-Subscript[zb,v]],Log[Subscript[z,w]]->Log[((1-yu)*yv*(1-yu*yw))/(yu*(1-yv)*(1-yv*yw))]-Log[Subscript[zb,w]],Log[1-Subscript[z,w]]->Log[((1-yu*yv)*(1-yu*yv*yw))/(yu*(1-yv)*(1-yv*yw))]-Log[1-Subscript[zb,w]],Log[z]->Log[((1-yv)*(1-yu*yv)*yw)/(yv*(1-yw)*(1-yu*yw))]-Log[zb],Log[1-z]->Log[((1-yv*yw)*(1-yu*yv*yw))/(yv*(1-yw)*(1-yu*yw))]-Log[1-zb]};
uToMRK={u->1-\[Xi],v->\[Xi] z zp,w->\[Xi](1-z)(1-zp)};
expandLogs={Log[a_ b_]:>Log[a]+Log[b],Log[Power[a_,b_]]:>b Log[a]};
toBinaryForm={HPL[word_,1-var_]:>Superscript[Subscript[h,FromDigits[word,2]],StringJoin["[",ToString[Length[word]],"]"]][var]}

coproductEntry[0,var_]:=0;
coproductEntry[func_,var_]:=coproductEntry[Expand[func],var]/;!MatchQ[Expand[func],func];
coproductEntry[func_,var_]:=(coproductEntry[func,var]=coproduct[{transcendentalWeight[func]-1,1},func]/.{CircleDot[x_,Log[var]]:>x,CircleDot[x__,Log[y_]]:>0/;y=!=var})/;FreeQ[func,CircleDot];
coproductEntry[func_,var_]:=If[(func/.{c_ CircleDot[x__,y_]:>transcendentalWeight[y],CircleDot[x__,y_]:>transcendentalWeight[y]})==1,func/.{CircleDot[x__,Log[y_]]:>0/;y=!=var,CircleDot[x__,Log[var]]:>CircleDot[x]},func/.{CircleDot[x__,Log[var]]:>CircleDot[x],CircleDot[__]:>0}]/;!FreeQ[func,CircleDot];

HPLfuncD[a_,{T,n_}]:=Nest[HPLfuncD[#,T]/.{HPL[{1},1/(T^2+1)]:>(Log[1+T^2]-2 Log[T])}&,a/.{HPL[{1},1/(T^2+1)]:>(Log[1+T^2]-2 Log[T])},n];
HPLfuncD[a_,{var_,n_}]:=Nest[HPLfuncD[#,var]&,a,n]/;var=!=T;
HPLfuncD[a_,var_]:=HPLfuncD[Expand[a],var]/;!MatchQ[a,Expand[a]];
HPLfuncD[Plus[a_,b__],var_]:=Sum[HPLfuncD[terms,var],{terms,{a,b}}];
HPLfuncD[Power[func_,n_],var_]:=n Power[func,n-1]HPLfuncD[func,var];
HPLfuncD[prefactor_,var_]:=D[prefactor,var]/;FreeQ[prefactor,HPL[__]]\[And]FreeQ[prefactor,Log[Temp]]\[And]FreeQ[prefactor,Alternatives@@allIrreducibleFunctions];
HPLfuncD[Times[hpl_,hplN__],var_]:=HPLfuncD[hpl,var] Times[hplN]+hpl HPLfuncD[Times[hplN],var];
HPLfuncD[HPL[{0},arg_],var_]:=D[arg,var]/(arg);
HPLfuncD[HPL[{1},arg_],var_]:=D[arg,var]/(1-arg);
HPLfuncD[HPL[{-1},arg_],var_]:=D[arg,var]/(1+arg);
HPLfuncD[HPL[{0,aVec__},arg_],var_]:=ReplaceAll[toStrictLyndonBasis[HPL[{aVec},arg]]*D[arg,var]/(arg),toHPL];
HPLfuncD[HPL[{1,aVec__},arg_],var_]:=ReplaceAll[toStrictLyndonBasis[HPL[{aVec},arg]]*D[arg,var]/(1-arg),toHPL];
HPLfuncD[HPL[{-1,aVec__},arg_],var_]:=ReplaceAll[toStrictLyndonBasis[HPL[{aVec},arg]]*D[arg,var]/(1+arg),toHPL];
HPLfuncD[func_,var_]:=Expand[coproductD[func,var]/.toHPL]/;MatchQ[func,Alternatives@@allIrreducibleFunctions];

(*HPLexpand[HPL[aVec_,HPLvar_],{var_,var0_,order_}]:=HPLexpand[HPL[aVec,HPLvar],{var,var0,order}]=Module[{newVar=Limit[HPLvar,var->var0],taylorExpansionTerm},
	taylorExpansionTerm[0]:=Normal[Series[HPL[aVec,HPLvar]/.{HPL[{0},var]:>Log[var],HPL[{1},var]:>-Log[1-var]},{var,var0,0}]];
	taylorExpansionTerm[n_]:=Normal[Series[Expand[HPLfuncD[HPL[aVec,HPLvar],{var,n}]]/.{HPL[{0},var]:>Log[var],HPL[{1},var]:>-Log[1-var],HPL[a_,v_]:>HPLexpand[HPL[a,v],{var,var0,n}]},{T,0,0}]]/;n>0;
	Sum[(var^n)taylorExpansionTerm[n]/(n!),{n,0,order}]];
HPLseries[func_,{var_,var0_,order_}]:=Module[{tempVar,function,termsList,expandToProperOrder},
	expandToProperOrder[term_]:=term/.{Power[var,n_]*remainder_:>(Power[var,n]remainder/.{HPL[aVec_,arg_]:>HPLexpand[HPL[aVec,arg/.tempVar->var],{var,var0,order-n}]}),var*remainder_:>(var*remainder/.{HPL[aVec_,arg_]:>HPLexpand[HPL[aVec,arg/.tempVar->var],{var,var0,order-1}]}),remainder_:>(remainder/.{HPL[aVec_,arg_]:>HPLexpand[HPL[aVec,arg/.tempVar->var],{var,var0,order}]})};function=Expand[Normal[Series[func/.HPL[aVec_,arg_]:>HPL[aVec,arg/.var->tempVar],{var,var0,order}]]];
	termsList=If[MatchQ[function,Plus[_,__]],List@@function,{function}];
	Expand[Normal[Series[Expand[Simplify[Plus@@(expandToProperOrder/@termsList)]],{var,var0,order}]]]];*)

expandHPL[order_:10]:={HPL[{0},z_]:>Log[z],HPL[aVec_,z_]:>HPLexpansion[compressedNotation[aVec],z,order]};
HPLexpansion[{m__},z_,order_]:=Sum[z^l*Z[{m},l],{l,1,order}];
Z[{m1_,mr__},j_]:=Rational[Sign[m1]^(j+1),j^Abs[m1]]Sum[Power[Sign[m1],l+1]Z[{mr},l-1],{l,2,j}];
Z[{m1_},j_]:=Rational[Power[Sign[m1],j+1],j^Abs[m1]]/;j>0;
Z[{m1_},j_]:=0/;j<=0;
(* old function names
expandHPL[{m__},z_,order_]:=Sum[z^l Z[{m},l],{l,1,order}]
expandTo[order_]:={HPL[{0},z_]:>Log[z],HPL[aVec_,z_]:>expandHPL[compressedNotation[aVec],z,order]};
expand={HPL[{0},z_]:>Log[z],HPL[aVec_,z_]:>expandHPL[compressedNotation[aVec],z,10]};*)

countLyndonBasis[n_,alphabet_]:=Block[{m=Length[alphabet],d=Divisors@n},Plus@@(MoebiusMu[n/d]*m^d/n)]; (*from Jeff*)
generateLyndonBasis[{n__},alphabet_]:=Block[{fullBasis=generateLyndonBasis[Max[List[n]],alphabet]},Sort[Join@@Table[Select[fullBasis,Length[#]==l&],{l,List[n]}]]];
generateLyndonBasis[n_,alphabet_]:= Module[{w={alphabet[[1]]},i,temp,list={{alphabet[[1]]}},pos,j=1,k=0,max},
	max=Sum[countLyndonBasis[k,alphabet],{k,1,n}];
	Reap[
		Sow[w];
		For[j=1,j<max,j++,
			temp=PadRight[{},n,w];
			While[temp[[-1]]==alphabet[[-1]],temp=Drop[temp,-1]];
			pos=Flatten[Position[alphabet,temp[[-1]]]][[1]];
			temp[[-1]]=alphabet[[pos+1]];
			Sow[w=temp];];][[2,1]]]/;!MatchQ[n,List[__]];(*from Jeff*)

asEquations[replacements_]:=(replacements/.Rule[a_,b_]:>(a-b));
asEquations[replacements1_,replacementsN__]:=asEquations[Join[replacements1,replacementsN]];
reduce[eqns_ ,ID_:mapleSolverID]:=Monitor[Module[{fullEqns=Normal[eqns],
	fileName=StringJoin["maple_equation_solver_",ToString[ID]],count=0,outputFile},
	initializing="writing equations to file";
	Put[fullEqns,fileName<>"_equations.dat"];
	Run["echo \"equations := $(cat "<>fileName<>"_equations.dat):\" > "<>fileName<>"_equations.dat"];
	Run["echo \"read \`"<>Directory[]<>"/"<>fileName<>"_equations.dat"<>"\`: \nsolution := solve(equations, remove(has,remove(has,indets(equations),z),Log[[Xi]])): \nsave(solution, \`"<>Directory[]<>"/"<>fileName<>"_solution.dat"<>"\`): \" > "<>fileName<>".mpl"];
    Monitor[Monitor[While[!FileExistsQ[fileName<>"_done.dat"],initializing=StringJoin["waiting for maple: ",ToString[count]," seconds"];count +=1;Pause[1]],Text["nohup maple -q "<>Directory[]<>"/"<>fileName<>".mpl > maple_solver.log &"]],Text["maple "<>Directory[]<>"/"<>fileName<>".mpl"]];
    Run["rm "<>fileName<>"_done.dat"];
	Run["sed -i '' 's/=/==/g' "<>fileName<>"_solution.dat"];
	Run["sed -i '' 's/:==/=/g' "<>fileName<>"_solution.dat"];
	initializing="loading in solutions";
	Run["sed -i '' 's/\\\//g' "<>fileName<>"_solution.dat"];
	Run["perl -p -i -e 's/\\R//g;' "<>fileName<>"_solution.dat"];
	Run["sed -i '' 's/Complex(\\([^)]*\\))/complex\\[\\1\\]/g' "<>fileName<>"_solution.dat"];
	Run["sed -i '' 's/Log\[\[Xi\]\]/Log\[\\[Xi\]\]/g' "<>fileName<>"_solution.dat"];
	Get[StringJoin[fileName,"_solution.dat"]];
	DeleteCases[solution/.complex[a_,b_]:>(a+b I)/.complex[b_]:>b I,True]/.Equal[a_,b_]:>Rule[a,b]],initializing];

evaluateG[funcName_,expression_,vars_,points_]:=Module[{formattedExpression,functionDirectory},
	functionDirectory=StringJoin["/Users/thatscottishkid/Google Drive/Stanford/Lance/Mathematica Library/ginac/",ToString[funcName]];
	formattedExpression=Expand[expression/.Table[vars[[ii]]->Evaluate[Symbol["var"<>ToString[ii]]],{ii,Length[vars]}]/.{Zeta[a_]:>zeta[a],\[Zeta][a_]:>zeta[a],\[Zeta][a__]:>\[Zeta]n[a]}];
	If[!DirectoryQ[functionDirectory],CreateDirectory[functionDirectory]];
    Export[StringJoin[functionDirectory,"/expression.dat"],formattedExpression];
	Export[StringJoin[functionDirectory,"/points.csv"],points];]

Gn[args__]:=Module[{},Gn[temp__]=.;
    Get[$MathematicaLibrary<>"/Function Library/GiNaC/Gn.m"];
    Gn[args]]/;$OperatingSystem=="Unix"

HtoEO = {H3[1] -> O3[1], H4[1] -> E4[1], H4[2] -> E4[2], H4[3] -> E4[3], 
     H4[4] -> O4[1], H4[5] -> O4[2], H4[6] -> O4[3], H5[7] -> E5[1], 
     H5[8] -> E5[2], H5[9] -> E5[3], H5[10] -> E5[4], H5[11] -> E5[5], 
     H5[12] -> E5[6], H5[13] -> E5[7], H5[14] -> E5[8], H5[15] -> E5[9], 
     H5[16] -> E5[10], H5[17] -> E5[11], H5[18] -> E5[12], H5[19] -> E5[13], 
     H5[1] -> O5[1], H5[2] -> O5[2], H5[3] -> O5[3], H5[4] -> O5[4], 
     H5[5] -> O5[5], H5[6] -> O5[6], H5[20] -> O5[7], H5[21] -> O5[8], 
     H5[22] -> O5[9], H5[23] -> O5[10], H6[1] -> E6[1], H6[2] -> E6[2], 
     H6[3] -> E6[3], H6[4] -> E6[4], H6[5] -> E6[5], H6[6] -> E6[6], 
     H6[7] -> E6[7], H6[8] -> E6[8], H6[9] -> E6[9], H6[10] -> E6[10], 
     H6[11] -> E6[11], H6[12] -> E6[12], H6[13] -> E6[13], H6[14] -> E6[14], 
     H6[15] -> E6[15], H6[16] -> E6[16], H6[17] -> E6[17], H6[18] -> E6[18], 
     H6[48] -> E6[19], H6[49] -> E6[20], H6[50] -> E6[21], H6[51] -> E6[22], 
     H6[52] -> E6[23], H6[53] -> E6[24], H6[54] -> E6[25], H6[55] -> E6[26], 
     H6[56] -> E6[27], H6[57] -> E6[28], H6[58] -> E6[29], H6[59] -> E6[30], 
     H6[60] -> E6[31], H6[61] -> E6[32], H6[62] -> E6[33], H6[63] -> E6[34], 
     H6[64] -> E6[35], H6[65] -> E6[36], H6[66] -> E6[37], H6[67] -> E6[38], 
     H6[68] -> E6[39], H6[69] -> E6[40], H6[70] -> E6[41], H6[71] -> E6[42], 
     H6[72] -> E6[43], H6[73] -> E6[44], H6[74] -> E6[45], H6[19] -> O6[1], 
     H6[20] -> O6[2], H6[21] -> O6[3], H6[22] -> O6[4], H6[23] -> O6[5], 
     H6[24] -> O6[6], H6[25] -> O6[7], H6[26] -> O6[8], H6[27] -> O6[9], 
     H6[28] -> O6[10], H6[29] -> O6[11], H6[30] -> O6[12], H6[31] -> O6[13], 
     H6[32] -> O6[14], H6[33] -> O6[15], H6[34] -> O6[16], H6[35] -> O6[17], 
     H6[36] -> O6[18], H6[37] -> O6[19], H6[38] -> O6[20], H6[39] -> O6[21], 
     H6[40] -> O6[22], H6[41] -> O6[23], H6[42] -> O6[24], H6[43] -> O6[25], 
     H6[44] -> O6[26], H6[45] -> O6[27], H6[46] -> O6[28], H6[47] -> O6[29], 
     H6[75] -> O6[30], H6[76] -> O6[31], H6[77] -> O6[32], H6[78] -> O6[33]};
