(* ::Package:: *)

ClearAll[LyndonBasis,outputAsLogs,IMPL,MPLtoIMPL,IMPLtoMPL,coproduct,quickCoproduct,maxCoproduct,transcendentalWeight,sumOverTwo,twoCoproduct,fullCoproduct,coproductTimes,CircleMinus,embedInCircleMinus,CircleDot,wordToMZV,LogsToIMPL,IMPLtoMZV,IMPLtoMZVtoZero,IMPLtoLogs,IMPLtoLyndonBasis,exteriorD,exteriorDifferentiation];

outputAsLogs=False;
LyndonBasis=True;

LogsToIMPL={Log[x_]:>IMPL[0,{0},x],PolyLog[n_,x_]:>(-IMPL[0,PadRight[{1},n],x])};
LogsToMPL={Log[1-x_]:>MPL[{0},1-x],Log[x_]:>MPL[{1},1-x],PolyLog[n_,x_]:>(-MPL[PadLeft[{1},n],x])};
MPLtoIMPL={MPL[aVector_,af_]:>IMPL[0,Reverse[aVector],af]};
IMPLtoMPL={IMPL[0,aVector_,af_]:>MPL[Reverse[aVector],af]};
IMPLtoMZVtoZero={IMPL[0,aVector_,1]->0};
wordToMZV[aVector_]:=Module[{pos},
	If[Length[aVector]==1,0,
		If[First[aVector]==1,pos=Position[aVector,1];\[Zeta]@@Flatten@Append[Table[pos[[i+1]]-pos[[i]],{i,Length@pos-1}],Length@aVector-Last[pos]+1],
			If[Last[aVector]==0,pos=Position[Table[1-i,{i,Reverse[aVector]}],1];\[Zeta]@@Flatten@Append[Table[pos[[i+1]]-pos[[i]],{i,Length@pos-1}],Length@aVector-Last[pos]+1],
	0]]]]; (* All functions IMPL[0,{0,...,1},1]=0, checked explicitly up to weight 10 For other identities see arXiv:1102.1310[math.NT] *)
IMPLtoMZV={IMPL[0,aVector_,1]:>wordToMZV[aVector]};
MPLtoLogs=Join[Table[MPL[PadLeft[{},i],y_]->Log[y]^i/(i!),{i,10}],Table[MPL[PadLeft[{},i,1],1-y_]->-(-Log[y])^i/(i!),{i,10}],Table[MPL[PadLeft[{1},i+1],y_]->-PolyLog[i+1,y],{i,0,9}]];
IMPLtoLogs=Join[Table[IMPL[0,PadLeft[{},i],y_]->Log[y]^i/(i!),{i,10}],Table[IMPL[0,PadLeft[{},i,1],1-y_]->-(-Log[y])^i/(i!),{i,10}],Table[IMPL[0,PadRight[{1},i+1],y_]->-PolyLog[i+1,y],{i,0,9}]];
MPLtoHPL={MPL[aVec_,af_]:>HPL[aVec,af](-1)^Total[aVec]};
HPLtoMPL={HPL[aVec_,af_]:>MPL[aVec,af](-1)^Total[aVec]};
<<canonicalIntegrationLimitsIMPL.m
If[!ValueQ[IMPLtoLyndonBasis[2]],
	<<LyndonBasis.m;
	IMPLtoLyndonBasisTemp=Join@@Table[IMPLtoLyndonBasis[i],{i,2,9}];];

transcendentalWeight[c_ func_]:=transcendentalWeight[func]/;NumericQ[c];
transcendentalWeight[Plus[x_,y__]]:=transcendentalWeight[x];
transcendentalWeight[func_]:=0/;NumericQ[func];
transcendentalWeight[H3[_]]:=3;
transcendentalWeight[H4[_]]:=4;
transcendentalWeight[H5[_]]:=5;
transcendentalWeight[H6[_]]:=6;
transcendentalWeight[H7[_]]:=7;
transcendentalWeight[H8[_]]:=8;
transcendentalWeight[H9[_]]:=9;
transcendentalWeight[H10[_]]:=10;
transcendentalWeight[func_]:=Abs[ReplaceAll[func/.LogsToIMPL/.MPLtoIMPL,IMPL[ai_,aVector_,af_]:>Length[aVector]]]/;!NumericQ[func]\[And]!MatchQ[func,Alternatives[H3[_],H4[_],H5[_],H6[_],H7[_],H8[_],H9[_],H10[_],Times[_,__],Power[_,_]]];
transcendentalWeight[Times[x_,y__]]:=Total[Abs[transcendentalWeight[#]&/@Select[List[x,y],!NumericQ[#]&]]]/;FreeQ[List[x,y],Power];
transcendentalWeight[Power[func_,n_]]:=n Abs[transcendentalWeight[func]]/;!MatchQ[func,Times[_,__]];
transcendentalWeight[Times[x___,Power[y_,n_],z___]]:=transcendentalWeight[Times[x,IMPL[0,Table[1,{i,n transcendentalWeight[y]}],Unique[]],z]];

coproduct[weights_:Null,Times[-1,func__]]:=-coproduct[weights,Times[func]];
coproduct[weights_:Null,func_]:=If[MemberQ[{func},Alternatives[H3[_],H4[_],H5[_],H6[_],H7[_],H8[_],H9[_],H10[_]],Infinity],irreducibleFunctionCoproduct[weights,func],
									If[weights===Null,fullCoproduct[func/.LogsToIMPL/.MPLtoIMPL],
										If[weights===max,maxCoproduct[func],
											If[Length[weights]==2,twoCoproduct[weights,func/.LogsToIMPL/.MPLtoIMPL,CircleMinus],
												If[Length[weights]>2,higherCoproduct[weights,func/.LogsToIMPL/.MPLtoIMPL]]]]]]/;!MatchQ[func,Times[-1,__]];

twoCoproduct[weights_,c_ func_,outputType_]:=c twoCoproduct[weights,func,outputType]/;NumericQ[c]\[And]!NumericQ[func];
twoCoproduct[weights_,IMPL[ai_,aVector_,af_],ouputType_]:=Print["The coproduct weights don't match the transcendental weight of this function"]/;Length[aVector]!=Total[weights];
twoCoproduct[{0,w_},IMPL[ai_,aVector_,af_],outputType_]:=outputType[1,IMPL[ai,aVector,af]]/;w!=0;
twoCoproduct[{w_,0},IMPL[ai_,aVector_,af_],outputType_]:=outputType[IMPL[ai,aVector,af],1]/;w!=0;
sumOverTwo[weights_]:=Module[{partitions=IntegerPartitions[Total[weights]+1],choose,allPermutations},
	choose=Select[partitions,Total[#]-Length[#]==Last@weights&];
	allPermutations=Join@@Table[Permutations[choose[[i]]],{i,Length@choose}];
	Table[Table[Total[Take[(allPermutations[[i]]),j]],{j,Length@allPermutations[[i]]-1}],{i,Length@allPermutations}]]
twoCoproduct[weights_,IMPL[ai_,aVector_,af_],ouputType_]:=Module[{vars=sumOverTwo[weights]},
	Sum[ouputType[IMPL[ai,Table[aVector[[vars[[i,j]]]],{j,Length[vars[[i]]]}],af],If[First[vars[[i]]]>1,IMPL[ai,Table[aVector[[l]],{l,First[vars[[i]]]-1}],aVector[[First[vars[[i]]]]]],1]Product[If[vars[[i,p]]<vars[[i,p+1]]-1,IMPL[aVector[[vars[[i,p]]]],Table[aVector[[l]],{l,vars[[i,p]]+1,vars[[i,p+1]]-1}],aVector[[vars[[i,p+1]]]]],1],{p,Length[vars[[i]]]-1}]If[Last[vars[[i]]]<Length[aVector],IMPL[aVector[[Last[vars[[i]]]]],Table[aVector[[l]],{l,Last[vars[[i]]]+1,Length[aVector]}],af],1]],{i,Length@vars}]]/;!MemberQ[weights,0];
twoCoproduct[weights_,Times[x_,y__],outputType_]:=Block[{functions,functionWeights,partitions,b},
	functions=List[x,y]/.LogsToIMPL/.MPLtoIMPL;
	functionWeights=ReplaceAll[functions,IMPL[ai_,aVector_,af_]:>Length[aVector]];
	partitions=Select[Flatten[Table[Array[b,Length@functions],##]&@@Table[{b[i],Max[0,Last@weights-Total[Drop[functionWeights,{i}]]],Min[functionWeights[[i]],Last@weights]},{i,Length@functions}],Length@functions-1],Total[#]==Last[weights]&];
combinedCoproduct[remainingFunctionWeights_,remainingPartitionWeights_,remainingFunctions_]:=coproductTimes[combinedCoproduct[Drop[remainingFunctionWeights,-1],Drop[remainingPartitionWeights,-1],Drop[remainingFunctions,-1]],twoCoproduct[{Last[remainingFunctionWeights]-Last[remainingPartitionWeights],Last[remainingPartitionWeights]},Last[remainingFunctions],CircleMinus]]/;Length@remainingFunctions>2;
combinedCoproduct[remainingFunctionWeights_,remainingPartitionWeights_,remainingFunctions_]:=coproductTimes[twoCoproduct[{First[remainingFunctionWeights]-First[remainingPartitionWeights],First[remainingPartitionWeights]},First[remainingFunctions],CircleMinus],twoCoproduct[{Last[remainingFunctionWeights]-Last[remainingPartitionWeights],Last[remainingPartitionWeights]},Last[remainingFunctions],CircleMinus]]/;Length@remainingFunctions==2;
	If[Total[weights]==Total[functionWeights],Sum[combinedCoproduct[functionWeights,partitions[[i]],functions],{i,Length@partitions}]//.{CircleMinus[f1_,f2_]:>outputType[f1,f2]},Print["The coproduct weights don't match the transcendental weight of this function"]]]/;FreeQ[List[x,y],Power];
twoCoproduct[weights_,Power[IMPL[0,aVector_,af_],n_],outputType_]:=Module[{dummyVars=Table[Unique[d],{i,n}]},
twoCoproduct[weights,Times@@Table[IMPL[0,aVector,dummyVars[[i]]],{i,n}],outputType]/.Table[dummyVars[[i]]->af,{i,n}]];
twoCoproduct[weights_,Times[x___,Power[IMPL[0,aVector_,af_],n_],y___],outputType_]:=Module[{dummyVars=Table[Unique[d],{i,n}]},
twoCoproduct[weights,Times@@Join[Table[IMPL[0,aVector,dummyVars[[i]]],{i,n}],{x,y}],outputType]/.Table[dummyVars[[i]]->af,{i,n}]];

higherCoproduct[weights_,func_]:=Module[{lastEntry,intermediate},
	lastEntry=twoCoproduct[{Total[Drop[weights,-1]],Last[weights]},func,intermediate];
	lastEntry/.{intermediate[x_,y_]:>CircleMinus[coproduct[Drop[weights,-1],x],y]}//Expand];

maxCoproduct[Plus[x_,y__]]:=Plus@@Table[maxCoproduct[List[x,y][[i]]],{i,Length@List[x,y]}];
maxCoproduct[c_ Plus[x_,y__]]:=c Plus@@Table[maxCoproduct[List[x,y][[i]]],{i,Length@List[x,y]}]/;NumericQ[c];
maxCoproduct[CircleDot[x__]]:=CircleDot@@Table[If[transcendentalWeight[List[x][[i]]]>1,coproduct[max,List[x][[i]]],List[x][[i]]],{i,Length@List[x]}];
maxCoproduct[c_ CircleDot[x__]]:=c CircleDot@@Table[If[transcendentalWeight[List[x][[i]]]>1,coproduct[max,List[x][[i]]],List[x][[i]]],{i,Length@List[x]}]/;NumericQ[c];
maxCoproduct[func_]:=Module[{w=transcendentalWeight[func]},
	If[w>1,coproduct[{Floor[w/2],Ceiling[w/2]},func]/.{CircleDot[x_,y_]:>CircleDot[coproduct[max,x],coproduct[max,y]]},func]]/;FreeQ[func,CircleDot[x__],Infinity];

fullCoproduct[Times[x_,y__]]:=coproductTimes[fullCoproduct[x],fullCoproduct[Times[y]]];
fullCoproduct[Power[x_,n_]]:=coproductTimes[fullCoproduct[x],fullCoproduct[Power[x,n-1]]];
fullCoproduct[IMPL[ai_,aVector_,af_]]:=Module[{kMax=Length@aVector,d},Sum[Sum[CircleMinus[IMPL[ai,Table[aVector[[d[i]]],{i,k}],af],If[d[1]>1,IMPL[ai,Table[aVector[[l]],{l,d[1]-1}],aVector[[d[1]]]],1]Product[If[d[i]<d[i+1]-1,IMPL[aVector[[d[i]]],Table[aVector[[l]],{l,d[i]+1,d[i+1]-1}],aVector[[d[i+1]]]],1],{i,k-1}]If[d[k]<kMax,IMPL[aVector[[d[k]]],Table[aVector[[l]],{l,d[k]+1,kMax}],af],1]],##]&@@Join[{{d[1],kMax}},Table[{d[j],d[j-1]+1,kMax},{j,2,k}]],{k,kMax}]]+CircleMinus[1,IMPL[ai,aVector,af]];

irreducibleFunctionCoproduct[{w_,1},Times[func1_,funcN__]]:=Sum[coproduct[{transcendentalWeight[f]-1,1},f]/.{CircleDot[x_,y_]:>CircleDot[Times@@DeleteCases[List[func1,funcN],f]x, y]},{f,List[func1,funcN]}];
irreducibleFunctionCoproduct[max,Times[func1_,funcN__]]:=Sum[coproduct[{transcendentalWeight[f]-1,1},f]/.{CircleDot[x_,y_]:>CircleDot[coproduct[max,Times@@DeleteCases[List[func1,funcN],f]x], y]},{f,List[func1,funcN]}];
irreducibleFunctionCoproduct[max,func_]:=coproduct[{transcendentalWeight[func]-1,1},func]/.CircleDot[x_,y_]:>CircleDot[coproduct[max,x],y];

CircleMinus[x_,y_]:=CircleMinus[x,Expand[y]]/;!MatchQ[y,Expand[y]];
CircleMinus[x_,y_]:=Plus@@Table[CircleMinus[x,y[[i]]],{i,Length[y]}]/;MatchQ[y,Plus[_,__]];
CircleMinus[x_,y_]:=-CircleMinus[-x,y]/;MatchQ[x,Times[-1,__]];
CircleMinus[x_,y_]:=-CircleMinus[x,-y]/;MatchQ[y,Times[-1,__]];
CircleMinus[x_,y_]:=0/;MatchQ[x/.{Power->Times},IMPL[0,_,0]]\[Or]MatchQ[y/.{Power->Times},IMPL[0,_,0]]\[Or]MatchQ[x/.{Power->Times},Times[IMPL[0,_,0],___]]\[Or]MatchQ[y/.{Power->Times},Times[IMPL[0,_,0],___]];
CircleMinus[x_,y_]:=(CircleDot[x/.IMPLtoMZV,y/.IMPLtoMZV]//.IMPLtoLogs/.IMPLtoMPL)/;outputAsLogs;
CircleMinus[x_,y_]:=(CircleDot[x/.IMPLtoMZV,y/.IMPLtoMZV]//.IMPLtoLyndonBasisTemp/.IMPLtoMPL)/;LyndonBasis\[And]!outputAsLogs;
CircleMinus[x_,y_]:=(CircleDot[x/.IMPLtoMZV,y/.IMPLtoMZV]/.IMPLtoMPL)/;!LyndonBasis\[And]!outputAsLogs;

CircleDot[x___,y_,z___]:=Plus@@Table[CircleDot[x,y[[i]],z],{i,Length[y]}]/;MatchQ[y,Plus[_,__]];
CircleDot[x___,c_ y_,z___]:=c CircleDot[x,y,z]/;NumericQ[c]\[And]!NumericQ[y];
CircleDot[x___,y_,z___]:=-CircleDot[x,-y,z]/;MatchQ[y,Times[-1,__]];
CircleDot[x___,CircleDot[y__],z___]:=CircleDot[x,y,z];
CircleDot[x___,0,z___]:=0;

coproductTimes[x_,y_]:=Plus@@Table[coproductTimes[x,y[[i]]],{i,Length[y]}]/;MatchQ[y,Plus[_,__]];
coproductTimes[x_,y_]:=Plus@@Table[coproductTimes[x[[i]],y],{i,Length[x]}]/;MatchQ[x,Plus[_,__]];
coproductTimes[c_ CircleDot[x__],y_]:=c coproductTimes[CircleDot[x],y]/;NumericQ[c];
coproductTimes[x_,c_ CircleDot[y__]]:=c coproductTimes[x,CircleDot[y]]/;NumericQ[c];
coproductTimes[x_,y_]:=-coproductTimes[x,-y]/;MatchQ[y,Times[-1,__]];
coproductTimes[fullCoproduct[c_],CircleDot[x__]]:=c CircleDot[x]/;NumericQ[c]; (*new!*)
coproductTimes[CircleDot[x1_,y1_],CircleDot[x2_,y2_]]:=CircleDot[x1 x2, y1 y2];
coproductTimes[x_,y_]:=0/;(x==0\[Or]y==0);

ClearAll[shuffleW,shuffleMPL,toLinearBasis]
shuffleW[s1_,s2_]:=Module[{p,tp,accf,ord},
	p=Permutations@Join[1&/@s1,0&/@s2];
	tp=BitXor[p,1];
	accf=Accumulate[#\[Transpose]]\[Transpose] #&;
	ord=accf[p]+(accf[tp]+Length[s1]) tp;
	Outer[Part,{Join[s1,s2]},ord,1]//First];
shuffleMPL[Plus[x_,y__]]:=Plus@@Table[shuffleMPL[i],{i,List[x,y]}];
shuffleMPL[Times[x___,MPL[aVector_,f_],y___,MPL[bVector_,f_],z___]]:=Module[{shuffles=shuffleW[aVector,bVector]},
	Sum[shuffleMPL[Times[x,y,z,MPL[shuffles[[i]],f]]],{i,Length@shuffles}]];
shuffleMPL[Times[x___,MPL[aVector_,f_],y___]]:=MPL[aVector,f] shuffleMPL[Times[x,y]]/;FreeQ[List[x,y],MPL[_,f],Infinity];
shuffleMPL[Power[MPL[aVector_,f_],n_]]:=Module[{shuffles,l,j},
	shuffles=shuffleW[aVector,aVector];
	For[l=2,l<n,l++,shuffles=Join@@Table[shuffleW[aVector,shuffles[[j]]],{j,Length@shuffles}]];
	Sum[MPL[shuffles[[j]],f],{j,Length@shuffles}]];
shuffleMPL[Times[x__,Power[MPL[aVector_,f_],n_]]]:=Module[{shuffles,l,j},
	shuffles=shuffleW[aVector,aVector];
	For[l=2,l<n,l++,shuffles=Join@@Table[shuffleW[aVector,shuffles[[j]]],{j,Length@shuffles}]];
	Sum[shuffleMPL[Times[x,MPL[shuffles[[j]],f]]],{j,Length@shuffles}]];
shuffleMPL[c_ MPL[aVector_,f_]]:=MPL[aVector,f]/.NumericQ[c];
shuffleMPL[MPL[aVector_,f_]]:=MPL[aVector,f];
shuffleMPL[c_]:=c/;NumericQ[c];

toLinearBasis[Times[a_,x__]]:=a toLinearBasis[Times[x]]/;NumericQ[a];
toLinearBasis[Plus[x_,y__]]:=Plus@@Table[toLinearBasis[i],{i,List[x,y]}];
toLinearBasis[CircleDot[x__]]:=CircleDot@@Table[shuffleMPL[List[x][[i]]],{i,Length@List[x]}];

yReplacements={yu->-((-1-u+v+w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])/(1+u-v-w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])),yv->-((-1+u-v+w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])/(1-u+v-w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])),yw->-((-1+u+v-w+Sqrt[-4*u*v*w+(-1+u+v+w)^2])/(1-u-v+w+Sqrt[-4*u*v*w+(-1+u+v+w)^2]))};
SubMinus[CircleDot[]]:=1;
SubPlus[CircleDot[]]:=1;
exteriorD[Plus[x_,y__],n_:max]:=Plus@@Table[exteriorD[List[x,y][[i]],n],{i,Length@List[x,y]}];
exteriorD[c_ Plus[x_,y__],n_:max]:=c Plus@@Table[exteriorD[List[x,y][[i]],n],{i,Length@List[x,y]}]/;NumericQ[c];
exteriorD[c_ CircleDot[x__],n_:max]:=c exteriorD[CircleDot[x],n]/;NumericQ[c];
exteriorD[CircleDot[x___,y_,z___],n_:max]:=exteriorD[CircleDot[x,coproduct[max,y]/.MPLtoLogs,z],n]/;transcendentalWeight[y]>1;
exteriorD[CircleDot[x___,MPL[{a_},af_],z___],n_:max]:=exteriorD[CircleDot[x,MPL[{a},af]/.MPLtoLogs,z],n];
exteriorD[CircleDot[x__,Log[y_],Log[z_]],last]:=SubMinus[CircleDot[x]]exteriorDifferentiation[CircleDot[Log[y],Log[z]]];
exteriorD[CircleDot[x__],max]:=Sum[exteriorD[CircleDot[x],i],{i,2,Length@List[x]}]/;FreeQ[List[x],MPL[a_,af_],Infinity];
exteriorD[CircleDot[x__],n_]:=If[n>Length@List[x]\[Or]n<2,Print["Cannot take the exterior derivative at the entry you specified."],SubMinus[CircleDot@@Take[List[x],n-2]]SubPlus[CircleDot@@Drop[List[x],n]]exteriorDifferentiation[CircleDot@@Join[Take[List[x],{n-1}],Take[List[x],{n}]]]]/;FreeQ[List[x],MPL[a_,af_],Infinity]\[And]n!=last;
exteriorDifferentiation[CircleDot[Log[x_],Log[y_]]]:=Module[{a=x/.yReplacements,b=y/.yReplacements},(D[Log[a],u]D[Log[b],v]-D[Log[b],u]D[Log[a],v])Wedge[du,dv]+(D[Log[a],u]D[Log[b],w]-D[Log[b],u]D[Log[a],w])Wedge[du,dw]+(D[Log[a],v]D[Log[b],w]-D[Log[b],v]D[Log[a],w])Wedge[dv,dw]]//Simplify;

cycle={u->v,v->w,w->u,yu->yv,yv->yw,yw->yu};
exchange[u,v]={u->v,v->u,yu->yv,yv->yu};
exchange[u,w]={u->w,w->u,yu->yw,yw->yu};
exchange[v,w]={v->w,w->v,yv->yw,yw->yv};

coproductEntry[func_,var_]:=func/.MPLtoLogs/.Join[{CircleDot[x__,Log[var]]:>If[Length@List[x]>1,CircleDot[x],x]},Table[CircleDot[x__,Log[i]]:>0,{i,DeleteCases[{u,v,w,1-u,1-v,1-w,yu,yv,yw},var]}]];
