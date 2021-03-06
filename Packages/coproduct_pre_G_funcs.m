(* ::Package:: *)

ClearAll[IMPL,MPL,MZV,MPLtoIMPL,IMPLtoMPL,coproduct,maxCoproduct,higherCoproduct,zetaValueCoproduct,transcendentalWeight,sumOverTwo,twoCoproduct,fullCoproduct,coproductTimes,CircleMinus,CircleDot,LogsToIMPL,IMPLtoMZVtoZero,IMPLtoLogs,LyndonBasisReplacements,completeLyndonBasisReplacements,exteriorD,exteriorDeriv,exteriorDifferentiation,coproductD,allIrreducibleFunctions,irreducibleFunctionCoproduct,shuffleW,shuffleMPL,toLinearBasis,cycle,exchange,yWeight,yGrading,replace\[CapitalDelta],coproductEntry,uReplacements,yReplacements,yMatchReplacements,Z,expand,expandTo,expandHPL,compressedNotation,toStrictLyndonBasis];

If[!ValueQ[stayInLyndonBasis],stayInLyndonBasis=True];
Do[Evaluate[Symbol["LyndonBasisReplacements"<>ToString[jj]<>"Ew"<>ToString[ii]<>"HPL"]]={},{ii,5,10},{jj,2,3}];
Do[Evaluate[Symbol["invertArgument"<>ToString[jj]<>"Ew"<>ToString[ii]<>"HPL"][x_, \[Delta]_]]={},{ii,5,10},{jj,2,3}];
Do[Evaluate[Symbol["toSingularArgN"<>ToString[jj]<>"Ew"<>ToString[ii]<>"HPL"][x_, \[Delta]_]]={},{ii,5,10},{jj,2,3}];
Do[Evaluate[Symbol["toSingularArgP2Ew"<>ToString[ii]<>"HPL"][x_, \[Delta]_]]={},{ii,5,10}];
Do[Evaluate[Symbol["flipArgument2Ew"<>ToString[ii]<>"HPL"][x_, \[Delta]_]]={},{ii,5,10}];
SVHPLreplacements={};

loadHPL2E[weight_:5]:=Module[{},
  If[(ValueQ[HPL2Eweight]\[And]weight>HPL2Eweight)\[Or]!ValueQ[HPL2Eweight],
     Do[Clear[Evaluate[Symbol["invertArgument2Ew"<>ToString[n]<>"HPL"]]];
        Clear[Evaluate[Symbol["toSingularArgN2Ew"<>ToString[n]<>"HPL"]]];
        Clear[Evaluate[Symbol["toSingularArgP2Ew"<>ToString[n]<>"HPL"]]];
        Clear[Evaluate[Symbol["flipArgument2Ew"<>ToString[n]<>"HPL"]]];
        Get["LyndonBasisReplacements2Ew"<>ToString[n]<>"HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
        Get["invertArgument2Ew"<>ToString[n]<>"HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
        Get["toSingularArgN2Ew"<>ToString[n]<>"HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
        Get["toSingularArgP2Ew"<>ToString[n]<>"HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
        Get["flipArgument2Ew"<>ToString[n]<>"HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
       ,{n,5,weight}];
     Unprotect[HPL2Eweight];
     HPL2Eweight=weight;
     Protect[HPL2Eweight];
     Print["HPL identities for letters {0,1} loaded through weight "<>ToString[HPL2Eweight]];
    ,Print["HPL identities for letters {0,1} already loaded through weight "<>ToString[HPL2Eweight]]]]/;10>=weight>=5;    

loadHPL3E[weight_:5]:=Module[{},
  If[(ValueQ[HPL3Eweight]\[And]weight>HPL3Eweight)\[Or]!ValueQ[HPL3Eweight],
     loadHPL2E[weight];
     Do[Clear[Evaluate[Symbol["invertArgument3Ew"<>ToString[n]<>"HPL"]]];
        Clear[Evaluate[Symbol["toSingularArgN3Ew"<>ToString[n]<>"HPL"]]];
        Get["LyndonBasisReplacements3Ew"<>ToString[n]<>"HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
        Get["invertArgument3Ew"<>ToString[n]<>"HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
        Get["toSingularArgN3Ew"<>ToString[n]<>"HPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
       ,{n,5,weight}];
     Unprotect[HPL3Eweight];
     HPL3Eweight=weight;
     Protect[HPL3Eweight];
     Print["HPL identities for letters {0,1,-1} loaded through weight "<>ToString[HPL3Eweight]];
    ,Print["HPL identities for letters {0,1,-1} already loaded through weight "<>ToString[HPL3Eweight]]]]/;10>=weight>=5;

loadMPL5E[weight_:5]:=Module[{},
  If[(ValueQ[MPL5Eweight]\[And]weight>MPL5Eweight)\[Or]!ValueQ[MPL5Eweight],
     Do[Get["LyndonBasisReplacements5Ew"<>ToString[n]<>"MPL_"<>ToString[Floor[$VersionNumber]]<>".mx"];
       ,{n,5,weight}];
     Unprotect[MPL5Eweight];
     MPL5Eweight=weight;
     Protect[MPL5Eweight];
     Print["MPL identities for letters {0,1,1/yu,1/yv,1/yu*yv} loaded through weight "<>ToString[MPL5Eweight]]]]/;10>=weight>=5;

LyndonBasisReplacements:=Flatten[Table[Symbol["LyndonBasisReplacements"<>ToString[jj]<>"Ew"<>ToString[ii]<>"HPL"],{ii,5,10},{jj,2,3}]];
invertArgument[x_, \[Delta]_:-1]:=Flatten[Table[Symbol["invertArgument"<>ToString[jj]<>"Ew"<>ToString[ii]<>"HPL"][x,\[Delta]],{ii,5,10},{jj,2,3}]];
toSingularArgN[x_, \[Delta]_:-1]:=Flatten[Table[Symbol["toSingularArgN"<>ToString[jj]<>"Ew"<>ToString[ii]<>"HPL"][x,\[Delta]],{ii,5,10},{jj,2,3}]];
toSingularArgP[x_, \[Delta]_:-1]:=Flatten[Table[Symbol["toSingularArgP2Ew"<>ToString[ii]<>"HPL"][x,\[Delta]],{ii,5,10}]];
flipArgument[x_, \[Delta]_:-1]:=Flatten[Table[Symbol["flipArgument2Ew"<>ToString[ii]<>"HPL"][x,\[Delta]],{ii,5,10}]];

Get["canonicalIntegrationLimits_"<>ToString[Floor[$VersionNumber]]<>".mx"]; (* original code in canonicalIntegrationLimitsIMPL.m *)
Get["coproductDerivatives.m"];
Get["functionConversions.m"];
Get["MZV2E.m"];
Get["MZV3E.m"];

HPL[aVec_,arg_]:=HPL[aVec,Simplify[arg]]/;!MatchQ[arg,Simplify[arg]];
HPL[{0},0]=-\[Zeta][1];
MPL[{0},0]=-\[Zeta][1];
HPL[{0},-1]=\[Delta]*I*Pi;
HPL[{___,1},0]=0;
MPL[{___,1},0]=0;
IMPL[0,{1,___},0]=0;
HPL[aVec_,1]:=((HPL[aVec,x]/.HPLtoIMPL)/.x->1);
HPL[aVec_,-1]:=((HPL[aVec,x]/.HPLtoIMPL)/.x->-1)/;Last[aVec]==1\[Or]Last[aVec]==-1;
MPL[aVec_,1]:=((MPL[aVec,x]/.MPLtoIMPL)/.x->1);
MPL[aVec_,-1]:=((MPL[aVec,x]/.MPLtoIMPL)/.x->-1)/;Last[aVec]==1\[Or]Last[aVec]==-1;
IMPL[0,aVec_,1]:=Expand[ReplaceAll[IMPL[0,aVec,\[CapitalIota]]/.LyndonBasisReplacements,IMPL[0,aVector_,\[CapitalIota]]:>IMPLwordToMZV[aVector]]];
IMPL[0,aVec_,-1]:=Expand[ReplaceAll[IMPL[0,-aVec,\[CapitalIota]]/.LyndonBasisReplacements,IMPL[0,aVector_,\[CapitalIota]]:>IMPLwordToMZV[aVector]]]
IMPLwordToMZV[aVector_]:=Module[{pos},If[Length[aVector]==1,Which[aVector=={1},-\[Zeta][1],aVector=={0},0,aVector=={-1},Log[2]],If[Abs[First[aVector]]==1,((-1)^Count[aVector,1])\[Zeta]@@compressedNotation[Reverse[aVector]]]]]; (*Module[{pos},If[Length[aVector]==1,If[aVector=={1},-\[Zeta][1],0],If[First[aVector]==1,pos=Position[aVector,1];((-1)^Count[aVector,1])\[Zeta]@@Reverse[Flatten[Append[Table[pos[[i+1]]-pos[[i]],{i,Length@pos-1}],Length@aVector-Last[pos]+1]]],If[Last[aVector]==0,pos=Position[Table[1-i,{i,Reverse[aVector]}],1];((-1)^Count[aVector,0])\[Zeta]@@Reverse[Flatten[Append[Table[pos[[i+1]]-pos[[i]],{i,Length@pos-1}],Length@aVector-Last[pos]+1]]],0]]]];*) (* All functions IMPL[0,{0,...,1},1]=0, checked explicitly up to weight 10 For other identities see arXiv:1102.1310[math.NT] *)
toMZVbasis={Power[HPL[{1},x_],n_]:>(n!)HPL[PadLeft[{},n,1],x], Power[HPL[{0},x_],n_]:>(-1)^(n)(n!)HPL[PadLeft[{},n,1],1-x], Power[MPL[{1},x_],n_]:>(n!)MPL[PadLeft[{},n,1],x], Power[MPL[{0},x_],n_]:>(n!)MPL[PadLeft[{},n,1],1-x]};

transcendentalWeight[Pi]:=1;
transcendentalWeight[\[Zeta][x__]]:=Total[Abs[List[x]]];
transcendentalWeight[SVHPL[x__]]:=Length[List[x]];
transcendentalWeight[c_ func_]:=transcendentalWeight[func]/;NumericQ[c]\[And]FreeQ[c,Pi];
transcendentalWeight[Plus[x_,y__]]:=transcendentalWeight[x];
transcendentalWeight[func_]:=0/;NumericQ[func]\[And]FreeQ[func,Pi];
transcendentalWeight[func_]:=Abs[ReplaceAll[func/.toIMPL,IMPL[ai_,aVector_,af_]:>Length[aVector]]]/;!NumericQ[func]\[And]!MatchQ[func,Alternatives@@Join[allIrreducibleFunctions,{Times[_,__],Power[_,_],CircleDot[_,__],SVHPL[__]}]];
transcendentalWeight[Times[HPL[aVec_,Power[x_,_]],y__]]:=transcendentalWeight[Times[HPL[aVec,x],y]];
transcendentalWeight[Times[MPL[aVec_,Power[x_,_]],y__]]:=transcendentalWeight[Times[MPL[aVec,x],y]];
transcendentalWeight[Times[IMPL[ai_,aVec_,Power[x_,_]],y__]]:=transcendentalWeight[Times[IMPL[ai,aVec,x],y]];
transcendentalWeight[Times[x_,y__]]:=Total[Abs[transcendentalWeight[#]&/@Select[List[x,y],!NumericQ[#]\[Or]MatchQ[#,Alternatives[Pi,Power[_,Pi]]]&]]]/;FreeQ[List[x,y],Power];
transcendentalWeight[Power[func_,n_]]:=n Abs[transcendentalWeight[func]]/;!MatchQ[func,Times[_,__]];
transcendentalWeight[Times[x___,Power[y_,n_],z___]]:=transcendentalWeight[Times[x,IMPL[0,Table[1,{i,n transcendentalWeight[y]}],Unique[]],z]];
transcendentalWeight[CircleDot[x_,y__]]:=Sum[transcendentalWeight[i],{i,List[x,y]}];

coproduct[weight_,0]:=0;
coproduct[weights_:Null,Times[-1,func__]]:=-coproduct[weights,Times[func]];
coproduct[weights_,Plus[x_,y__]]:=Sum[coproduct[weights,i],{i,List[x,y]}];
coproduct[weights_,c_ Plus[x_,y__]]:=c Sum[coproduct[weights,i],{i,List[x,y]}]/;NumericQ[c]\[And]FreeQ[c,Pi];
coproduct[weights_,c_ CircleDot[x_,y__]]:=c coproduct[weights,CircleDot[x,y]]/;NumericQ[c]\[And]FreeQ[c,Pi];
coproduct[weights_,CircleDot[x_,y__]]:=CircleDot[x,y]/;(transcendentalWeight/@List[x,y])==weights;
coproduct[weights_,CircleDot[Power[Pi,n_],y__]]:=coproduct[weights,CircleDot[Power[Pi,n]/.\[Pi]to\[Zeta],y]];
coproduct[max,CircleDot[x_,y__]]:=CircleDot@@Table[coproduct[max,f],{f,List[x,y]}];
coproduct[weights_:Null,func_]:=Expand[If[MemberQ[{func},Alternatives[\[Zeta][__],Pi],Infinity],zetaValueCoproduct[weights,func/.{Pi->\[Zeta][0,1,0]}]/.{\[Zeta][0,1,0]->Pi},
									If[MemberQ[{func},Alternatives@@allIrreducibleFunctions,Infinity],irreducibleFunctionCoproduct[weights,func],
										If[weights===Null,fullCoproduct[func/.SVHPLreplacements/.toIMPL],
											If[weights===max,maxCoproduct[Expand[func]],
												If[Length[weights]==2,twoCoproduct[weights,func/.SVHPLreplacements/.toIMPL,CircleMinus],
													If[Length[weights]>2,higherCoproduct[weights,func/.SVHPLreplacements/.toIMPL]]]]]]]]/;!MatchQ[func,Times[-1,__]]\[And]FreeQ[func,CircleDot];

twoCoproduct[weights_,0,outputType_]:=0;
twoCoproduct[weights_,c_ func_,outputType_]:=c twoCoproduct[weights,func,outputType]/;NumericQ[c]\[And]FreeQ[c,Pi]\[And]!NumericQ[func];
twoCoproduct[weights_,IMPL[ai_,aVector_,af_],ouputType_]:=Print[StringJoin["The coproduct weights ",ToString[weights]," don't match the transcendental weight of the function ",ToString[IMPL[ai,aVector,af]]]]/;Length[aVector]!=Total[weights];
twoCoproduct[{0,w_},IMPL[ai_,aVector_,af_],outputType_]:=outputType[1,IMPL[ai,aVector,af]]/;w!=0;
twoCoproduct[{w_,0},IMPL[ai_,aVector_,af_],outputType_]:=outputType[IMPL[ai,aVector,af],1]/;w!=0;
sumOverTwo[weights_]:=Module[{partitions=IntegerPartitions[Total[weights]+1],choose,allPermutations},
	choose=Select[partitions,Total[#]-Length[#]==Last@weights&];
	allPermutations=Join@@Table[Permutations[choose[[i]]],{i,Length@choose}];
	Table[Table[Total[Take[(allPermutations[[i]]),j]],{j,Length@allPermutations[[i]]-1}],{i,Length@allPermutations}]]
twoCoproduct[weights_,IMPL[ai_,aVector_,af_],ouputType_]:=Module[{vars=sumOverTwo[weights]},
	Sum[ouputType[IMPL[ai,Table[aVector[[vars[[i,j]]]],{j,Length[vars[[i]]]}],af],If[First[vars[[i]]]>1,IMPL[ai,Table[aVector[[l]],{l,First[vars[[i]]]-1}],aVector[[First[vars[[i]]]]]],1]Product[If[vars[[i,p]]<vars[[i,p+1]]-1,IMPL[aVector[[vars[[i,p]]]],Table[aVector[[l]],{l,vars[[i,p]]+1,vars[[i,p+1]]-1}],aVector[[vars[[i,p+1]]]]],1],{p,Length[vars[[i]]]-1}]If[Last[vars[[i]]]<Length[aVector],IMPL[aVector[[Last[vars[[i]]]]],Table[aVector[[l]],{l,Last[vars[[i]]]+1,Length[aVector]}],af],1]],{i,Length@vars}]]/;!MemberQ[weights,0];
twoCoproduct[weights_,Times[x_,y__],outputType_]:=Block[{functions,functionWeights,partitions,combinedCoproduct,b},
	functions=List[x,y]/.SVHPLreplacements/.toIMPL;
	functionWeights=ReplaceAll[functions,IMPL[ai_,aVector_,af_]:>Length[aVector]];
	partitions=Select[Flatten[Table[Array[b,Length@functions],##]&@@Table[{b[i],Max[0,Last@weights-Total[Drop[functionWeights,{i}]]],Min[functionWeights[[i]],Last@weights]},{i,Length@functions}],Length@functions-1],Total[#]==Last[weights]&];	
	combinedCoproduct[remainingFunctionWeights_,remainingPartitionWeights_,remainingFunctions_]:=coproductTimes[combinedCoproduct[Drop[remainingFunctionWeights,-1],Drop[remainingPartitionWeights,-1],Drop[remainingFunctions,-1]],twoCoproduct[{Last[remainingFunctionWeights]-Last[remainingPartitionWeights],Last[remainingPartitionWeights]},Last[remainingFunctions],CircleMinus]]/;Length@remainingFunctions>2;
	combinedCoproduct[remainingFunctionWeights_,remainingPartitionWeights_,remainingFunctions_]:=coproductTimes[twoCoproduct[{First[remainingFunctionWeights]-First[remainingPartitionWeights],First[remainingPartitionWeights]},First[remainingFunctions],CircleMinus],twoCoproduct[{Last[remainingFunctionWeights]-Last[remainingPartitionWeights],Last[remainingPartitionWeights]},Last[remainingFunctions],CircleMinus]]/;Length@remainingFunctions==2;
	If[Total[weights]==Total[functionWeights],Sum[combinedCoproduct[functionWeights,partitions[[i]],functions],{i,Length@partitions}]//.{CircleMinus[f1_,f2_]:>outputType[f1,f2]},Print[StringJoin["The coproduct weights ",ToString[weights]," don't match the transcendental weight of the function ",ToString[Times[x,y]]]]]]/;FreeQ[List[x,y],Power,Infinity]\[And]Select[List[x,y],NumericQ[#]&]=={};
twoCoproduct[weights_,Power[IMPL[0,aVector_,af_],n_],outputType_]:=Module[{dummyVars=Table[Unique[d],{i,n}]}, twoCoproduct[weights,Times@@Table[IMPL[0,aVector,dummyVars[[i]]],{i,n}],outputType]/.Table[dummyVars[[i]]->af,{i,n}]];
twoCoproduct[weights_,Times[x___,Power[IMPL[0,aVector_,af_],n_],y___],outputType_]:=Module[{dummyVars=Table[Unique[d],{i,n}]}, twoCoproduct[weights,Times@@Join[Table[IMPL[0,aVector,dummyVars[[i]]],{i,n}],{x,y}],outputType]/.Table[dummyVars[[i]]->af,{i,n}]];
twoCoproduct[weights_,Times[x___,IMPL[0,aVector_,Power[af_,n_]],y___],outputType_]:=Module[{tempVar},twoCoproduct[weights,Times[x,IMPL[0,aVector,tempVar],y],outputType]/.{tempVar->Power[af,n]}];

higherCoproduct[weights_,func_]:=Module[{lastEntry,intermediate},
	lastEntry=twoCoproduct[{Total[Drop[weights,-1]],Last[weights]},func,intermediate];
	lastEntry/.{intermediate[x_,y_]:>CircleMinus[coproduct[Drop[weights,-1],x],y]}//Expand];

maxCoproduct[CircleDot[x__]]:=CircleDot@@Table[If[transcendentalWeight[List[x][[i]]]>1\[And]!MatchQ[List[x][[i]],pureMZV],coproduct[max,List[x][[i]]],List[x][[i]]],{i,Length@List[x]}];
maxCoproduct[c_ CircleDot[x__]]:=c CircleDot@@Table[If[transcendentalWeight[List[x][[i]]]>1\[And]!MatchQ[List[x][[i]],pureMZV],coproduct[max,List[x][[i]]],List[x][[i]]],{i,Length@List[x]}]/;NumericQ[c]\[And]FreeQ[c,Pi];
maxCoproduct[func_]:=Module[{w=transcendentalWeight[func]}, If[w>1\[And]!MatchQ[func,pureMZV],coproduct[{Floor[w/2],Ceiling[w/2]},func]/.{CircleDot[x_,y_]:>CircleDot[coproduct[max,x],coproduct[max,y]]},func]]/;FreeQ[func,CircleDot[x__],Infinity];

fullCoproduct[Times[x_,y__]]:=coproductTimes[fullCoproduct[x],fullCoproduct[Times[y]]];
fullCoproduct[Power[x_,n_]]:=coproductTimes[fullCoproduct[x],fullCoproduct[Power[x,n-1]]];
fullCoproduct[IMPL[ai_,aVector_,af_]]:=Module[{kMax=Length@aVector,d},Sum[Sum[CircleMinus[IMPL[ai,Table[aVector[[d[i]]],{i,k}],af],If[d[1]>1,IMPL[ai,Table[aVector[[l]],{l,d[1]-1}],aVector[[d[1]]]],1]Product[If[d[i]<d[i+1]-1,IMPL[aVector[[d[i]]],Table[aVector[[l]],{l,d[i]+1,d[i+1]-1}],aVector[[d[i+1]]]],1],{i,k-1}]If[d[k]<kMax,IMPL[aVector[[d[k]]],Table[aVector[[l]],{l,d[k]+1,kMax}],af],1]],##]&@@Join[{{d[1],kMax}},Table[{d[j],d[j-1]+1,kMax},{j,2,k}]],{k,kMax}]]+CircleMinus[1,IMPL[ai,aVector,af]];

irreducibleFunctionCoproduct[weights_,Times[c_,funcN__]]:=c irreducibleFunctionCoproduct[weights,Times[funcN]]/;NumericQ[c]\[And]FreeQ[c,Pi];
irreducibleFunctionCoproduct[{w__,1},func_]:=(irreducibleFunctionCoproduct[{transcendentalWeight[func]-1,1},func]/.{CircleDot[x_,y_]:>CircleDot[coproduct[{w},x],y]})/;Length[List[w]]>1\[And]MemberQ[allIrreducibleFunctions,func];
irreducibleFunctionCoproduct[{w__,1},Times[func1_,funcN__]]:=Sum[coproduct[{transcendentalWeight[f]-1,1},f]/.{CircleDot[x_,y_]:>CircleDot[Times@@DeleteCases[List[func1,funcN],f]x, y]},{f,List[func1,funcN]}]/;Select[List[func1,funcN],NumericQ[#]&]=={};
irreducibleFunctionCoproduct[{w__,1},Power[func_,n_]]:=Expand[n coproduct[{transcendentalWeight[func]-1,1},func]/.{CircleDot[x_,y_]:>CircleDot[x Power[func,n-1],y]}];
irreducibleFunctionCoproduct[max,Times[func1_,funcN__]]:=Sum[coproduct[{transcendentalWeight[f]-1,1},f]/.{CircleDot[x_,y_]:>CircleDot[coproduct[max,Times@@DeleteCases[List[func1,funcN],f]x], y]},{f,List[func1,funcN]}]/;Select[List[func1,funcN],NumericQ[#]&]=={};
irreducibleFunctionCoproduct[max,func_]:=coproduct[{transcendentalWeight[func]-1,1},func]/.CircleDot[x_,y_]:>CircleDot[coproduct[max,x],y];

zetaValueCoproduct[weights_,0]=0;
zetaValueCoproduct[weights_,c_ func_]:=c zetaValueCoproduct[weights,func]/;NumericQ[c]\[And]FreeQ[c,Pi];
zetaValueCoproduct[max,x_]:=CircleDot[x]/;MatchQ[x,pureMZV];
zetaValueCoproduct[max,Times[func_,x_]]:=(coproduct[{transcendentalWeight[Times[func,x]]-1,1},Times[func,x]]/.{CircleDot[a_,b_]:>CircleDot[coproduct[max,a],b]})/;MatchQ[x,pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]MemberQ[{func},Alternatives@@allIrreducibleFunctions,Infinity];
zetaValueCoproduct[max,Times[func_,x_]]:=CircleDot[x,coproduct[max,func]]/;MatchQ[x,pureMZV]\[And]FreeQ[func,Alternatives@@Append[allIrreducibleFunctions,\[Zeta][__]]];
zetaValueCoproduct[weights_,x_]:=If[First[weights]==transcendentalWeight[x]\[And]DeleteCases[Drop[weights,1],0]=={},CircleDot[x],0]/;MatchQ[x,pureMZV]\[And]weights=!=Alternatives[Null,max];
zetaValueCoproduct[weights_,Times[func_,\[Zeta][n__]]]:=splitCoproduct[weights,func,\[Zeta][n]]/;MatchQ[Times[\[Zeta][n]],pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]weights=!=Alternatives[Null,max];
zetaValueCoproduct[weights_,Times[func_,\[Zeta][n1__]\[Zeta][n2__]]]:=splitCoproduct[weights,func,\[Zeta][n1]\[Zeta][n2]]/;MatchQ[Times[\[Zeta][n1]\[Zeta][n2]],pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]weights=!=Alternatives[Null,max];
zetaValueCoproduct[weights_,Times[func_,\[Zeta][n1__]\[Zeta][n2__]\[Zeta][n3__]]]:=splitCoproduct[weights,func,\[Zeta][n1]\[Zeta][n2]\[Zeta][n3]]/;MatchQ[Times[\[Zeta][n1]\[Zeta][n2]\[Zeta][n3]],pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]weights=!=Alternatives[Null,max];
zetaValueCoproduct[weights_,Times[func_,\[Zeta][n1__]\[Zeta][n2__]\[Zeta][n3__]\[Zeta][n4__]]]:=splitCoproduct[weights,func,\[Zeta][n1]\[Zeta][n2]\[Zeta][n3]\[Zeta][n4]]/;MatchQ[Times[\[Zeta][n1]\[Zeta][n2]\[Zeta][n3]],pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]weights=!=Alternatives[Null,max];
zetaValueCoproduct[weights_,Times[func_,Power[\[Zeta][n__],m_]]]:=splitCoproduct[weights,func,Power[\[Zeta][n],m]]/;MatchQ[Times[Power[\[Zeta][n],m]],pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]weights=!=Alternatives[Null,max];
zetaValueCoproduct[weights_,Times[func_,\[Zeta][n1__]Power[\[Zeta][n2__],m_]]]:=splitCoproduct[weights,func,\[Zeta][n1]Power[\[Zeta][n2],m]]/;MatchQ[Times[\[Zeta][n1]Power[\[Zeta][n2],m]],pureMZV]\[And]FreeQ[func,\[Zeta][__]]\[And]weights=!=Alternatives[Null,max];
splitCoproduct[weights_,func_,pureConstant_]:=Module[{\[Zeta]weight=transcendentalWeight[pureConstant]},
	Which[\[Zeta]weight<First[weights], coproduct[Prepend[Drop[weights,1],First[weights]-\[Zeta]weight],func]/.{CircleDot[x_,y_]:>CircleDot[Times[pureConstant, x],y]},
			\[Zeta]weight==First[weights]\[And]Length[weights]==2\[And]Total[Drop[weights,1]]==transcendentalWeight[func], CircleDot[pureConstant,func],
			\[Zeta]weight==First[weights]\[And]Length[weights]>2, CircleDot[pureConstant,coproduct[Drop[weights,1],func]],
			\[Zeta]weight>First[weights],0,
			Total[weights]!=transcendentalWeight[func],Print[StringJoin["The coproduct weights ",ToString[weights]," don't match the transcendental weight of the function ",ToString[Times[pureConstant,func]]]]]];

CircleMinus[x_,y_]:=CircleMinus[x,Expand[y]]/;!MatchQ[y,Expand[y]];
CircleMinus[x_,y_]:=Plus@@Table[CircleMinus[x,y[[i]]],{i,Length[y]}]/;MatchQ[y,Plus[_,__]];
CircleMinus[x_,y_]:=-CircleMinus[-x,y]/;MatchQ[x,Times[-1,__]];
CircleMinus[x_,y_]:=-CircleMinus[x,-y]/;MatchQ[y,Times[-1,__]];
CircleMinus[x_,y_]:=0/;MatchQ[x/.{Power->Times},IMPL[0,_,0]]\[Or]MatchQ[y/.{Power->Times},IMPL[0,_,0]]\[Or]MatchQ[x/.{Power->Times},Times[IMPL[0,_,0],___]]\[Or]MatchQ[y/.{Power->Times},Times[IMPL[0,_,0],___]];
CircleMinus[x_,y_]:=toStrictLyndonBasis[CircleDot[x,y/.{\[Zeta][__]->0}]]/;stayInLyndonBasis;
CircleMinus[x_,y_]:=(CircleDot[x,y/.{\[Zeta][__]->0}]/.IMPLtoMPL)/;!stayInLyndonBasis;

CircleDot[y_,z__]:=CircleDot[Expand[y],z]/;!MatchQ[y,Expand[y]];
CircleDot[x__,y_]:=CircleDot[x,Expand[y]]/;!MatchQ[y,Expand[y]];
CircleDot[x__,y_,z__]:=CircleDot[x,Expand[y],z]/;!MatchQ[y,Expand[y]];
CircleDot[x___,y_,z___]:=Plus@@Table[CircleDot[x,y[[i]],z],{i,Length[y]}]/;MatchQ[y,Plus[_,__]];
CircleDot[x___,c_ y_,z___]:=c CircleDot[x,y,z]/;NumericQ[c]\[And]FreeQ[c,Pi]\[And]!NumericQ[y];
CircleDot[x___,y_,z___]:=-CircleDot[x,-y,z]/;MatchQ[y,Times[-1,__]];
CircleDot[x___,CircleDot[y__],z___]:=CircleDot[x,y,z];
CircleDot[x___,y1_ y2__,z___]:=y1 CircleDot[x,y2,z]/;NumberQ[y1];
CircleDot[x___,0,z___]:=0;

coproductTimes[x_,y_]:=Plus@@Table[coproductTimes[x,y[[i]]],{i,Length[y]}]/;MatchQ[y,Plus[_,__]];
coproductTimes[x_,y_]:=Plus@@Table[coproductTimes[x[[i]],y],{i,Length[x]}]/;MatchQ[x,Plus[_,__]];
coproductTimes[c_ CircleDot[x__],y_]:=c coproductTimes[CircleDot[x],y]/;NumericQ[c]\[And]FreeQ[c,Pi];
coproductTimes[x_,c_ CircleDot[y__]]:=c coproductTimes[x,CircleDot[y]]/;NumericQ[c]\[And]FreeQ[c,Pi];
coproductTimes[x_,y_]:=-coproductTimes[x,-y]/;MatchQ[y,Times[-1,__]];
coproductTimes[fullCoproduct[c_],CircleDot[x__]]:=c CircleDot[x]/;NumericQ[c]\[And]FreeQ[c,Pi]; (*new!*)
coproductTimes[CircleDot[x1_,y1_],CircleDot[x2_,y2_]]:=CircleDot[x1 x2, y1 y2];
coproductTimes[x_,y_]:=0/;(x==0\[Or]y==0);

shuffleW[s1_,s2_]:=Module[{p,tp,accf,ord}, p=Permutations@Join[1&/@s1,0&/@s2]; tp=BitXor[p,1]; accf=Accumulate[#\[Transpose]]\[Transpose] #&; ord=accf[p]+(accf[tp]+Length[s1]) tp; Outer[Part,{Join[s1,s2]},ord,1]//First];
shuffleMPL[Plus[x_,y__]]:=Plus@@Table[shuffleMPL[i],{i,List[x,y]}];
shuffleMPL[Times[x___,MPL[aVector_,f_],y___,MPL[bVector_,f_],z___]]:=Module[{shuffles=shuffleW[aVector,bVector]},Sum[shuffleMPL[Times[x,y,z,MPL[shuffles[[i]],f]]],{i,Length@shuffles}]];
shuffleMPL[Times[x___,MPL[aVector_,f_],y___]]:=MPL[aVector,f] shuffleMPL[Times[x,y]]/;FreeQ[List[x,y],MPL[_,f],Infinity];
shuffleMPL[Power[MPL[aVector_,f_],n_]]:=Module[{shuffles,l,j}, shuffles=shuffleW[aVector,aVector]; For[l=2,l<n,l++,shuffles=Join@@Table[shuffleW[aVector,shuffles[[j]]],{j,Length@shuffles}]]; Sum[MPL[shuffles[[j]],f],{j,Length@shuffles}]];
shuffleMPL[Times[x__,Power[MPL[aVector_,f_],n_]]]:=Module[{shuffles,l,j}, shuffles=shuffleW[aVector,aVector]; For[l=2,l<n,l++,shuffles=Join@@Table[shuffleW[aVector,shuffles[[j]]],{j,Length@shuffles}]]; Sum[shuffleMPL[Times[x,MPL[shuffles[[j]],f]]],{j,Length@shuffles}]];
shuffleMPL[c_ MPL[aVector_,f_]]:=MPL[aVector,f]/;NumericQ[c];
shuffleMPL[MPL[aVector_,f_]]:=MPL[aVector,f];
shuffleMPL[c_]:=c/;NumericQ[c];
shuffleMPL[rational_]:=rational/;FreeQ[rational,MPL[_,_]];
shuffleMPL[\[Zeta][x__]]:=\[Zeta][x];
shuffleMPL[\[Zeta][x__]^n_]:=\[Zeta][x]^n;
shuffleMPL[\[Zeta][x__]func_]:=\[Zeta][x]shuffleMPL[func];
shuffleMPL[\[Zeta][x__]^n_ func_]:=\[Zeta][x]^n shuffleMPL[func];

toLinearBasis[Times[a_,x__]]:=a toLinearBasis[Times[x]]/;NumericQ[a];
toLinearBasis[Plus[x_,y__]]:=Sum[toLinearBasis[i],{i,List[x,y]}];
toLinearBasis[Times[x__,Plus[y_,z__]]]:=toLinearBasis[Expand[Times[x,Plus[y,z]]]]/;!Or@@NumericQ/@List[x];
toLinearBasis[func_]:=shuffleMPL[func/.toMPL]/;!MatchQ[func,Alternatives[Times[x_,y__]/;NumericQ[x],Plus[_,__],CircleDot[__]]];
toLinearBasis[CircleDot[x__]]:=CircleDot@@Table[shuffleMPL[List[x][[i]]/.toMPL],{i,Length@List[x]}];
toLyndonBasis[func_]:=func/.toIMPL/.LyndonBasisReplacements/.IMPLtoMPL;
strictLyndonBasisReplacements={IMPL[0, {0, 0}, y_] -> IMPL[0, {0}, y]^2/2, IMPL[0, {1, 1}, y_] -> IMPL[0, {1}, y]^2/2, IMPL[0, {-1, -1}, y_] -> IMPL[0, {-1}, y]^2/2, IMPL[0, {0, 0, 0}, y_] -> IMPL[0, {0}, y]^3/6,  IMPL[0, {1, 1, 1}, y_] -> IMPL[0, {1}, y]^3/6, IMPL[0, {-1, -1, -1}, y_] -> IMPL[0, {-1}, y]^3/6, IMPL[0, {0, 0, 0, 0}, y_] -> IMPL[0, {0}, y]^4/24, IMPL[0, {1, 1, 1, 1}, y_] -> IMPL[0, {1}, y]^4/24, IMPL[0, {-1, -1, -1, -1}, y_] -> IMPL[0, {-1}, y]^4/24, IMPL[0, {0, 0, 0, 0, 0}, y_] -> IMPL[0, {0}, y]^5/120, IMPL[0, {1, 1, 1, 1, 1}, y_] -> IMPL[0, {1}, y]^5/120, IMPL[0, {-1, -1, -1, -1, -1}, y_] -> IMPL[0, {-1}, y]^5/120, IMPL[0, {0, 0, 0, 0, 0, 0}, y_] -> IMPL[0, {0}, y]^6/720, IMPL[0, {1, 1, 1, 1, 1, 1}, y_] -> IMPL[0, {1}, y]^6/720, IMPL[0, {-1, -1, -1, -1, -1, -1}, y_] -> IMPL[0, {-1}, y]^6/720, IMPL[0, {0, 0, 0, 0, 0, 0, 0}, y_] -> IMPL[0, {0}, y]^7/5040, IMPL[0, {1, 1, 1, 1, 1, 1, 1}, y_] -> IMPL[0, {1}, y]^7/5040, IMPL[0, {-1, -1, -1, -1, -1, -1, -1}, y_] -> IMPL[0, {-1}, y]^7/5040, IMPL[0, {0, 0, 0, 0, 0, 0, 0, 0}, y_] -> IMPL[0, {0}, y]^8/40320, IMPL[0, {1, 1, 1, 1, 1, 1, 1, 1}, y_] -> IMPL[0, {1}, y]^8/40320, IMPL[0, {-1, -1, -1, -1, -1, -1, -1, -1}, y_] -> IMPL[0, {-1}, y]^8/40320, IMPL[0, {0, 0, 0, 0, 0, 0, 0, 0, 0}, y_] -> IMPL[0, {0}, y]^9/362880, IMPL[0, {1, 1, 1, 1, 1, 1, 1, 1, 1}, y_] -> IMPL[0, {1}, y]^9/362880, IMPL[0, {-1, -1, -1, -1, -1, -1, -1, -1, -1}, y_] -> IMPL[0, {-1}, y]^9/362880, IMPL[0, {0, 0, 0, 0, 0, 0, 0, 0, 0, 0}, y_] -> IMPL[0, {0}, y]^10/3628800, IMPL[0, {1, 1, 1, 1, 1, 1, 1, 1, 1, 1}, y_] -> IMPL[0, {1}, y]^10/3628800, IMPL[0, {-1, -1, -1, -1, -1, -1, -1, -1, -1, -1}, y_] -> IMPL[0, {-1}, y]^10/3628800};
toStrictLyndonBasis[func_]:=func/.toIMPL/.LyndonBasisReplacements/.strictLyndonBasisReplacements/.IMPLtoMPL;

checkIntegrability[func_,max]:=Module[{maxCoproduct,checkEntries,weight=transcendentalWeight[func]},
	maxCoproduct=coproduct[max,func]/.toLogs/.\[Pi]to\[Zeta]/.{CircleDot[a_,b__]:>a checkIntegrability[CircleDot[b],max]/;MatchQ[a,pureMZV]\[And]Length[List[b]]>1,CircleDot[a_,b__]:>0/;MatchQ[a,pureMZV]\[And]Length[List[b]]==1};
	checkEntries[m_]:=maxCoproduct/.{CircleDot[a___,Log[b_],Log[c_],d___]:>SubMinus[CircleDot[a]]SubPlus[CircleDot[d]]AngleBracket[b,c]/;Length[List[a]]==m-1\[And]Length[List[d]]==weight-1-m};
	Sum[Expand[checkEntries[i]],{i,weight-1}]];
checkIntegrability[func_,last]:=Expand[func/.CircleDot[x_,y_]:>CircleDot[coproduct[{transcendentalWeight[func]-2,1},x],y]/.CircleDot[a__,b_,c_]:>CircleDot[a,b/.toLogs,c/.toLogs]/.\[Pi]to\[Zeta]/.{CircleDot[a___,Log[b_],Log[c_]]:>CircleDot[a]AngleBracket[b,c]}/.toHPL/.flipArgument[{u,v,w}]/.CircleDot[a__]:>toLinearBasis[CircleDot[a]]];

yReplacements={yu->-((-1-u+v+w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])/(1+u-v-w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])),yv->-((-1+u-v+w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])/(1-u+v-w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])),yw->-((-1+u+v-w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])/(1-u-v+w+Sqrt[-4*u*v*w+(-1+u+v+w)^2]))};
uReplacements={1-u->(1-yu)(1-yu yv yw)/((1-yu yv)(1-yu yw)),1-v->(1-yv)(1-yu yv yw)/((1-yv yu)(1-yv yw)),1-w->(1-yw)(1-yu yv yw)/((1-yw yu)(1-yw yv)),u->yu(1-yv)(1-yw)/((1-yu yv)(1-yu yw)),v->yv(1-yu)(1-yw)/((1-yv yu)(1-yv yw)),w->yw(1-yu)(1-yv)/((1-yw yu)(1-yw yv))};
\[Xi]replacements={Subscript[\[Xi],u]->((1-yu)*(1-yu*yv*yw))/((1-yu*yv)*(1-yu*yw)),Subscript[\[Xi],v]->((1-yv)*(1-yu*yv*yw))/((1-yu*yv)*(1-yv*yw)),Subscript[\[Xi],w]->((1-yw)*(1-yu*yv*yw))/((1-yu*yw)*(1-yv*yw)),\[Xi]->((1-yu)*(1-yu*yv*yw))/((1-yu*yv)*(1-yu*yw))};
zLogReplacements = {Log[Subscript[z,u]]->Log[((1-yv)*(1-yu*yv)*yw)/(yv*(1-yw)*(1-yu*yw))]-Log[Subscript[zb,u]],Log[1-Subscript[z,u]]->Log[((1-yv*yw)*(1-yu*yv*yw))/(yv*(1-yw)*(1-yu*yw))]-Log[1-Subscript[zb,u]],Log[Subscript[z,v]]->Log[(yu*(1-yw)*(1-yv*yw))/((1-yu)*(1-yu*yv)*yw)]-Log[Subscript[zb,v]],Log[1-Subscript[z,v]]->Log[((1-yu*yw)*(1-yu*yv*yw))/((1-yu)*(1-yu*yv)*yw)]-Log[1-Subscript[zb,v]],Log[Subscript[z,w]]->Log[((1-yu)*yv*(1-yu*yw))/(yu*(1-yv)*(1-yv*yw))]-Log[Subscript[zb,w]],Log[1-Subscript[z,w]]->Log[((1-yu*yv)*(1-yu*yv*yw))/(yu*(1-yv)*(1-yv*yw))]-Log[1-Subscript[zb,w]],Log[z]->Log[((1-yv)*(1-yu*yv)*yw)/(yv*(1-yw)*(1-yu*yw))]-Log[zb],Log[1-z]->Log[((1-yv*yw)*(1-yu*yv*yw))/(yv*(1-yw)*(1-yu*yw))]-Log[1-zb]};
yMatchReplacements={ -((-1 - u + v + w + Sqrt[-4*u*v*w + (-1 + u + v + w)^2])/(1 + u - v - w + Sqrt[-4*u*v*w + (-1 + u + v + w)^2]))->yu,-((-1+u-v+w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])/(1-u+v-w+Sqrt[-4*u*v*w+(-1+u+v+w)^2]))->yv,-((-1+u+v-w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])/(1-u-v+w+Sqrt[-4*u*v*w+(-1+u+v+w)^2]))->yw};
uToMRK={u->1-\[Xi],v->\[Xi] z zp,w->\[Xi](1-z)(1-zp)};
expandLogs={Log[a_ b_]:>Log[a]+Log[b],Log[Power[a_,b_]]:>b Log[a]};

cycle={u->v,v->w,w->u,yu->yv,yv->yw,yw->yu};
exchange[u,v]={u->v,v->u,yu->yv,yv->yu};
exchange[u,w]={u->w,w->u,yu->yw,yw->yu};
exchange[v,w]={v->w,w->v,yv->yw,yw->yv};
exchangeSP[u,v]={u-v->u-v,u->v,v->u};
yWeight[1]={yu,yv,yw};
Do[yWeight[i]={};,{i,2,8}];
yGrading[func_]:=Module[{entries,gradings,k,yCount},
	yCount[f_]:=Sum[k Count[f,Alternatives@@yWeight[k],Infinity],{k,8}]+Sum[k(n-1)Count[f,Alternatives@@Power[yWeight[k],n],Infinity],{n,2,3},{k,8}];
	If[MatchQ[Expand[func],Plus[_,__]],entries=List@@Expand[func],entries={func}]/.{c_ CircleDot[x__]:>CircleDot[x]};
	gradings=Table[yCount[{k}],{k,entries}];
	If[And@@(EvenQ/@gradings)\[Or]And@@(OddQ/@gradings),Max[gradings],Print["Function has mixed parity."]]];
Do[Get["weight_"<>ToString[i]<>"_irreducible_basis_functions_wfec.dat"],{i,5}]
Do[Get["weight_"<>ToString[i]<>"_irreducible_functions_wfec.dat"],{i,7}];

coproductEntry[0,var_]:=0;
coproductEntry[func_,var_]:=coproductEntry[Expand[func],var]/;!MatchQ[Expand[func],func];
coproductEntry[Plus[func1_,funcN__],var_]:=Sum[coproductEntry[i,var],{i,List[func1,funcN]}];
coproductEntry[func_,var_]:=Expand[Module[{functionCoproduct},
	functionCoproduct=Which[MatchQ[func,Alternatives[CircleDot[__,_],Times[__,CircleDot[__,_]]]]\[And](func/.{c_ CircleDot[x__,y_]:>transcendentalWeight[y],CircleDot[x__,y_]:>transcendentalWeight[y]})==1,func,
							MatchQ[func,Alternatives[CircleDot[__,_],Times[__,CircleDot[__,_]]]]\[And](func/.{c_ CircleDot[x__,y_]:>transcendentalWeight[y],CircleDot[x__,y_]:>transcendentalWeight[y]})>1,func/.{CircleDot[x__,y_]:>CircleDot[x,coproduct[{transcendentalWeight[y]-1,1},y]]},
							!MatchQ[func,Alternatives[CircleDot[__,_],Times[__,CircleDot[__,_]]]],coproduct[{transcendentalWeight[func]-1,1},func]];
	functionCoproduct/.toLogs/.{CircleDot[x__,Log[var]]:>If[Length@List[x]>1,CircleDot[x],x],CircleDot[x__,Log[y_]]:>0/;y=!=var}]/.LogsToHPL/.flipArgument[{u,v,w}]/.toMPL];

IntegrateHPL[func_,{var_,ll_,ul_}]:=Sum[IntegrateHPL[i,{var,ll,ul}],{i,List@@Expand[func]}]/;MatchQ[Expand[func],Plus[_,__]];
IntegrateHPL[c_ func_,{var_,ll_,ul_}]:=Expand[c IntegrateHPL[func,{var,ll,ul}]]/;NumericQ[c];
IntegrateHPL[func_,{var_,ll_,ul_}]:=IntegrateHPL[func,{var,0,ul}]-IntegrateHPL[func,{var,0,ll}]/;ll=!=0;
IntegrateHPL[func_,{var_,0,0}]:=0;
IntegrateHPL[func_,{var_,0,ul_}]:=Expand[toStrictLyndonBasis[Expand[Apart[toLinearBasis[Expand[func/.toHPL/.flipArgument[1-var]]/.toHPL/.flipArgument[1-var]],var]]/.toHPL/.{Times[f_,Power[var-1,-1]]:>-Times[f,Power[1-var,-1]]}/.{(HPL[aVec_,var]/var):>HPL[Prepend[aVec,0],lTemp],(HPL[aVec_,var]/(1-var)):>HPL[Prepend[aVec,1],lTemp],1/var:>HPL[{0},lTemp],1/(1-var):>HPL[{1},lTemp]}]/.lTemp->ul/.toHPL]/;(!MatchQ[Expand[func],Plus[_,__]]\[And]ul=!=0\[And]FreeQ[func,Alternatives@@allIrreducibleFunctions]);

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

symbolLevelFunctionsWeight[n_]:=symbolLevelFunctionsWeight[n]=If[n>2\[And]basis===Lbasis,Join[Get["weight_"<>ToString[n]<>"_HPL_basis_wfec.dat"],Get["weight_"<>ToString[n]<>"_composite_basis_functions_wfec.dat"],Get["weight_"<>ToString[n]<>"_irreducible_basis_functions_wfec.dat"]],Join[Get["weight_"<>ToString[n]<>"_HPL_basis_wfec.dat"],Get["weight_"<>ToString[n]<>"_composite_functions_wfec.dat"],Get["weight_"<>ToString[n]<>"_irreducible_functions_wfec.dat"]]];
beyondSymbolTerms[weight_]:=beyondSymbolTerms[weight]=Module[{functionsOfWeight,beyondSymbolFunctions},Do[functionsOfWeight[n]=symbolLevelFunctionsWeight[n],{n,weight-2}];beyondSymbolFunctions=Flatten[Table[Table[MZV[weight-n][[j]]symbolLevelFunctionsWeight[n][[k]],{k,Length[symbolLevelFunctionsWeight[n]]},{j,Length[MZV[weight-n]]}],{n,weight-2}]]; Join[Reverse@beyondSymbolFunctions,MZV[weight]]];
functionsWeight[n_]:=functionsWeight[n]=If[n>2\[And]basis===Lbasis,Join[Get["weight_"<>ToString[n]<>"_HPL_basis_wfec.dat"],Get["weight_"<>ToString[n]<>"_composite_basis_functions_wfec.dat"],Get["weight_"<>ToString[n]<>"_irreducible_basis_functions_wfec.dat"],beyondSymbolTerms[n]],Join[Get["weight_"<>ToString[n]<>"_HPL_basis_wfec.dat"],Get["weight_"<>ToString[n]<>"_composite_functions_wfec.dat"],Get["weight_"<>ToString[n]<>"_irreducible_functions_wfec.dat"],beyondSymbolTerms[n]]];

expandHPL[order_:10]:={HPL[{0},z_]:>Log[z],HPL[aVec_,z_]:>HPLexpansion[compressedNotation[aVec],z,order]};
HPLexpansion[{m__},z_,order_]:=Sum[z^l Z[{m},l],{l,1,order}];
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

HPLtoG[m_,x_]:=HPLtoG[m,x]=(-1)^Count[m,1]Fold[IntG,1,Reverse[a]/.{0->x,1->1-x}]
IntG[a_,u]:=IntG[a,yu]+IntG[a,1-yv]-IntG[a,1-yu yv]+IntG[a,1-yw]-IntG[a,1-yu yw]
IntG[a_,v]:=IntG[a,1-yu]+IntG[a,yv]-IntG[a,1-yu yv]+IntG[a,1-yw]-IntG[a,1-yv yw]
IntG[a_,w]:=IntG[a,1-yu]+IntG[a,1-yv]+IntG[a,yw]-IntG[a,1-yu yw]-IntG[a,1-yv yw]
IntG[a_,1-u]:=IntG[a,1-yu]-IntG[a,1-yu yv]-IntG[a,1-yu yw]+IntG[a,1-yu yv yw]
IntG[a_,1-v]:=IntG[a,1-yv]-IntG[a,1-yu yv]-IntG[a,1-yv yw]+IntG[a,1-yu yv yw]
IntG[a_,1-w]:=IntG[a,1-yw]-IntG[a,1-yu yw]-IntG[a,1-yv yw]+IntG[a,1-yu yv yw]
IntG[a_,yu]:=IntGImpl[a/.G[b__,yv]:>0/.G[b__,yw]:>0,yu,0]
IntG[a_,yv]:=IntGImpl[a/.G[b__,yw]:>0,yv,0]
IntG[a_,yw]:=IntGImpl[a,yw,0]
IntG[a_,1-yu]:=IntGImpl[a/.G[b__,yv]:>0/.G[b__,yw]:>0,yu,1]
IntG[a_,1-yv]:=IntGImpl[a/.G[b__,yw]:>0,yv,1]
IntG[a_,1-yw]:=IntGImpl[a,yw,1]
IntG[a_,1-yu yv]:=IntGImpl[a/.G[b__,yw]:>0,yv,1/yu]
IntG[a_,1-yu yw]:=IntGImpl[a,yw,1/yu]
IntG[a_,1-yv yw]:=IntGImpl[a,yw,1/yv]
IntG[a_,1-yu yv yw]:=IntGImpl[a,yw,1/yu/yv]
