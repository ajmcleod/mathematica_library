(* ::Package:: *)

ClearAll[currentWeight,basis,simplifiedSymbol,symbolWrap,fastExteriorD,initializeFastExteriorD,fastExteriorDReplacement,appendPreviousWeightSymbol,\[CapitalDelta],setVariables,variables,differentials,twoForms,derivatives,logD,logDmod,exteriorD,checkSymbol,toSymbol,u,v,w]

imposeFirstEntryCondition=True;

setVariables[a_:u]:=(
	Print["Variable choice not recognized..."]
	setVariables[u];/!(a===y););

setVariables[u]:=(
	variables={u,v,w}; 
	differentials={du,dv,dw}; 
	firstEntries={u,v,w};
	middleEntries={u,v,w,1-u,1-v,1-w,yu,yv,yw};
	twoForms=Flatten[Table[Wedge[differentials[[i]],differentials[[j]]],{i,Length@differentials},{j,i+1,Length@differentials}]];
	derivatives[u]={(1-u-v-w)/(u Sqrt[\[CapitalDelta]]),(1-u-v+w)/((1-u)Sqrt[\[CapitalDelta]]),(1-u+v-w)/((1-u)Sqrt[\[CapitalDelta]])}; 
	derivatives[v]={(1-u-v+w)/((1-v)Sqrt[\[CapitalDelta]]),(1-u-v-w)/(v Sqrt[\[CapitalDelta]]),(1+u-v-w)/((1-v)Sqrt[\[CapitalDelta]])}; 
	derivatives[w]={(1-u+v-w)/((1-w)Sqrt[\[CapitalDelta]]),(1+u-v-w)/((1-w)Sqrt[\[CapitalDelta]]),(1-u-v-w)/(w Sqrt[\[CapitalDelta]])};
	Print["u, v, and w variables adopted"]);
\[CapitalDelta]=(1-u-v-w)^2 - 4 u v w;

setVariables[y]:=(
	variables={yu,yv,yw}; 
	differentials={dyu,dyv,dyw}; 
	firstEntries={yu(1-yv)(1-yw)/((1-yu yv)(1-yu yw)),yv(1-yw)(1-yu)/((1-yv yw)(1-yv yu)),yw(1-yu)(1-yv)/((1-yw yu)(1-yw yv))};
	middleEntries={yu,yv,yw,1-yu,1-yv,1-yw,1-yu yv,1-yu yw,1-yv yw,1-yu yv yw};
	twoForms=Flatten[Table[Wedge[differentials[[i]],differentials[[j]]],{i,Length@differentials},{j,i+1,Length@differentials}]];
	Print["yu, yv, and yw variables adopted"])

logD[x_,y_]:=If[variables[[1]]===yu,D[Log[x],y],logDmod[x,y]]
logDmod[Times[x1___,x2_,x3___],y_]:=logDmod[Times[x1,x3],y]+logDmod[x2,y]/;(x2===yu\[Or]x2===yv\[Or]x2===yw)
logDmod[Times[x1___,Power[x2_,n_],x3___],y_]:=logDmod[Times[x1,x3],y]+n logDmod[x2,y]/;(x2===yu\[Or]x2===yv\[Or]x2===yw)
logDmod[Times[Power[x2_,n_]],y_]:= n logDmod[x2,y]/;(x2===yu\[Or]x2===yv\[Or]x2===yw)
logDmod[x_,y_]:=D[Log[x],y]/;(!MatchQ[x,Times[___,yu]]\[And]!MatchQ[x,Times[___,yv]]\[And]!MatchQ[x,Times[___,yw]]\[And]!MatchQ[x,yu]\[And]!MatchQ[x,yv]\[And]!MatchQ[x,yw])
logDmod[x_,y_]:= Part[derivatives[y],ReplaceAll[x,{yu->1,yv->2,yw->3}]]/;(MatchQ[x,yu]\[Or]MatchQ[x,yv]\[Or]MatchQ[x,yw])

exteriorD[x_,m_]:=Plus@@Table[exteriorD[Apply[List,x][[i]],m],{i,Length@Apply[List,x]}]/;MatchQ[x,Plus[_,__]]
exteriorD[Times[-1,x_],m_]:=-exteriorD[x,m]/;MatchQ[x,CircleTimes[__]]
exteriorD[Times[a_,x_],m_]:=a exteriorD[x,m]/;MatchQ[x,CircleTimes[__]]
exteriorD[x_,m_]:=Block[{prefix,suffix},
	prefix=If[m>2,SubPlus[CircleTimes@@Take[List@@x,m-2]],1];
	suffix=If[m<Length@Apply[List,x],SubMinus[CircleTimes@@Take[List@@x,-Length@Apply[List,x]+m]],1];
	(prefix)(suffix)Sum[(logD[x[[m-1]],variables[[i]]]logD[x[[m]],variables[[j]]]-logD[x[[m-1]],variables[[j]]]logD[x[[m]],variables[[i]]])Wedge[differentials[[i]],differentials[[j]]],{i,1,3},{j,i+1,3}]]/;!MatchQ[x,Plus[_,__]]

fastExteriorD[x_]:=Plus@@Table[fastExteriorD[Apply[List,x][[i]]],{i,Length@Apply[List,x]}]/;MatchQ[x,Plus[_,__]]
fastExteriorD[Times[a_,x_]]:=a fastExteriorD[x]/;MatchQ[x,CircleTimes[__]]\[And]!MatchQ[x,Plus[_,__]]
fastExteriorD[x_]:=Block[{baseSymbol},
	baseSymbol=ReplaceAll[x,CircleTimes[DoubleBracketingBar[a__],__]->a];
	fastExteriorDReplacement[baseSymbol,First@Take[x,{-2}],First@Take[x,{-1}]]
	]/;(MatchQ[x,CircleTimes[__]]\[And]currentWeight>2)
fastExteriorD[x_]:=Block[{},
	fastExteriorDReplacement[2,First@Take[x,{-2}],First@Take[x,{-1}]]
	]/;(MatchQ[x,CircleTimes[__]]\[And]currentWeight==2)
	
checkSymbol[x_]:= checkSymbol[Expand[x]]/;!MatchQ[x,Expand[x]]
checkSymbol[Plus[x_,y_]]:=Plus[checkSymbol[x],checkSymbol[y]]
checkSymbol[a_ CircleTimes[x__]]:=a checkSymbol[CircleTimes[x]]/;NumericQ[a]
checkSymbol[x_]:=Sum[DoubleBracketingBar[Table[(List@@x)[[j]],{j,1,i}]]exteriorD[x,2+i] DoubleBracketingBar[Table[(List@@x)[[j]],{j,i+3,Length[List@@x]}]],{i,0,Length[List@@x]-2}]/;MatchQ[x,CircleTimes[___]]

TrueSymbol=1;
defineSymbol:=(
	ClearAll[symbol,symbolShuffle,CircleTimes,toSymbol,symbolWrap,shuffleTemp,shuffleWrap];
	SetAttributes[{symbol,symbolShuffle},{Flat,OneIdentity}];
	SetAttributes[CircleTimes,OneIdentity];
	
	simplifiedSymbol[x_]:=symbolWrap[symbol[x]];
	symbol[c_]:=0/;NumericQ[c];
	symbol[x_]:=symbol[Expand[x]]/;!MatchQ[x,Expand[x]];
	symbol[x_+y_]:=symbol[x]+symbol[y];
	symbol[Zeta[x__] y___]:=0/;!ValueQ[TrueSymbol]\[Or]TrueSymbol==1;
	symbol[Zeta[x__]]:=0/;!ValueQ[TrueSymbol]\[Or]TrueSymbol==1;
	symbol[Times[x_,y_]]:=x symbol[y]/;NumericQ[x]&&!NumericQ[y];
	symbol[Times[x_,y_]]:=shuffleWrap[symbolShuffle[symbol[x],symbol[y]]]/;!NumericQ[x]&&!NumericQ[y];
	symbol[Power[y_,n_]]:=shuffleWrap[symbolShuffle@@Table[symbol[y],{i,1,n}]];
	symbol[Log[x_]]:=CircleTimes[x];
	symbol[PolyLog[n_,x_]]:=-CircleTimes@@Join[{1-x},Table[x,{i,n-1}]];
	symbol[MPL[a_,y_]]:=CircleTimes[First@a-y]-CircleTimes[First@a]/;Length@a==1;
	symbol[MPL[a_,y_]]:=CircleTimes[symbol[MPL[Drop[a,1],y]],First@Take[a,{1}]-y]-CircleTimes[symbol[MPL[Drop[a,1],y]],First@Take[a,{1}]-First@Take[a,{2}]]+Plus@@Table[CircleTimes[symbol[MPL[Drop[a,{i}],y]],First@Take[a,{i}]-First@Take[a,{i-1}]]-CircleTimes[symbol[MPL[Drop[a,{i}],y]],First@Take[a,{i}]-First@Take[a,{i+1}]],{i,2,Length@a-1}]+CircleTimes[symbol[MPL[Drop[a,-1],y]],First@Take[a,{-1}]-First@Take[a,{-2}]]-CircleTimes[symbol[MPL[Drop[a,-1],y]],First@Take[a,{-1}]]/;Length@a>1;
	
	symbolShuffle[x___,0,y___]:=0;
	symbolShuffle[x___,a_ Plus[y__],z___]:=a symbolShuffle[x,Plus[y],z]/;NumericQ[a];
	symbolShuffle[x___,Plus[y1_,y2__],z___]:= Plus@@Table[symbolShuffle[x,i,z],{i,List[y1,y2]}];
	symbolShuffle[x___,a_ CircleTimes[y__],z___]:=a symbolShuffle[x,CircleTimes[y],z]/;NumericQ[a];
	symbolShuffle[x___,CircleTimes[y__],z___]:=symbolShuffle[x,shuffleTemp[y],z];
	symbolShuffle[shuffleTemp[x0_,x1___],shuffleTemp[y0_,y1___],z___]:=symbolShuffle[shuffleTemp[x0,symbolShuffle[shuffleTemp[x1],shuffleTemp[y0,y1]]],z]+symbolShuffle[shuffleTemp[y0,symbolShuffle[shuffleTemp[x0,x1],shuffleTemp[y1]]],z];
	symbolShuffle[x___,shuffleTemp[],y___]:=symbolShuffle[x,y];
	symbolShuffle[shuffleTemp[x__]]:=shuffleTemp[x];
	shuffleTemp[x___,shuffleTemp[y__],z___]:=shuffleTemp[x,y,z];
	shuffleTemp[x___,a_ shuffleTemp[y__],z___]:=a shuffleTemp[x,y,z]/;NumericQ[a];
	shuffleTemp[x___,Plus[shuffleTemp[t__],y___],z___]:=shuffleTemp[x,t,z]+shuffleTemp[x,Plus[y],z];
	shuffleTemp[x___,Plus[a_ shuffleTemp[t__],y___],z___]:=a shuffleTemp[x,t,z]+shuffleTemp[x,Plus[y],z]/;NumericQ[a];
	shuffleWrap[Plus[x_,y__]]:=Plus@@Table[shuffleWrap[i],{i,List[x,y]}];
	shuffleWrap[a_ Plus[x_,y__]]:=a Plus@@Table[shuffleWrap[i],{i,List[x,y]}]/;NumericQ[a];
	shuffleWrap[a_ shuffleTemp[x__]]:=a shuffleWrap[shuffleTemp[x]]/;NumericQ[a];
	shuffleWrap[shuffleTemp[x__]]:=CircleTimes[x]/;FreeQ[List[x],shuffleTemp[___]];

	CircleTimes[x__,y_,z___]:=Plus@@Table[CircleTimes[x,y[[i]],z],{i,Length[y]}]/;MatchQ[y,Plus[CircleTimes[__],__]];
	CircleTimes[x___,y_,z__]:=Plus@@Table[CircleTimes[x,y[[i]],z],{i,Length[y]}]/;MatchQ[y,Plus[CircleTimes[__],__]];
	CircleTimes[x__,CircleTimes[y__],z___]:=CircleTimes[x,y,z];
	CircleTimes[x___,CircleTimes[y__],z__]:=CircleTimes[x,y,z];
	CircleTimes[x___,y_,z___]:=CircleTimes[x,Factor[y],z]/;!MatchQ[y,Factor[y]]; (*break into cases if recursion is problematic*)
	CircleTimes[x___,Times[y1_,y2__],z___]:=y1 CircleTimes[x,y2,z]/;(!MatchQ[y1,CircleTimes[___]]\[And]MatchQ[First@List[y2],CircleTimes[___]]); (*last change: added First@List[] to var y2. Also on line below*)
	CircleTimes[x___,Times[y1_,y2__],z___]:=CircleTimes[x,y1,z]+CircleTimes[x,Times[y2],z]/;(!MatchQ[y1,CircleTimes[___]]\[And]!MatchQ[First@List[y2],CircleTimes[___]]);
	CircleTimes[x___,Power[y_,-1],z___]:=-CircleTimes[x,y,z];
	CircleTimes[x__,y_,z___]:=CircleTimes[x,Plus@@Sort[List@@y],z]/;MatchQ[y,Plus[_,__]]&&!MatchQ[List@@y,Sort[List@@y]];
	CircleTimes[x___,y_,z__]:=CircleTimes[x,Plus@@Sort[List@@y],z]/;MatchQ[y,Plus[_,__]]&&!MatchQ[List@@y,Sort[List@@y]];
	CircleTimes[x___,y_,z___]:=CircleTimes[x,-y,z]/;MatchQ[y,Plus[_,__]]&&MatchQ[First[Sort[List@@y]],Times[-1,__]];
	(*CircleTimes[x___,y_,z__]:=CircleTimes[x,-y,z]/;MatchQ[y,Plus[_,__]]&&MatchQ[First[Sort[List@@y]],Times[-1,__]];
	CircleTimes[x__,y_,z___]:=CircleTimes[x,-y,z]/;MatchQ[y,Plus[_,__]]&&Negative[First[Sort[List@@y]]];*)
	CircleTimes[x___,y_,z___]:=CircleTimes[x,-y,z]/;MatchQ[y,Plus[_,__]]&&Negative[First[Sort[List@@y]]];
	CircleTimes[x_]:=CircleTimes[-x]/;MatchQ[x,Plus[_,__]]&&Negative[First[Sort[List@@x]]];
	CircleTimes[x__,y_,z___]:=0/;(NumericQ[y]\[Or]MatchQ[y,DirectedInfinity[_]]);
	CircleTimes[x___,y_,z__]:=0/;(NumericQ[y]\[Or]MatchQ[y,DirectedInfinity[_]]);
	CircleTimes[x_]:=0/;NumericQ[x];
	symbolWrap[x_]:=FullSimplify[x];

	toSymbol[c_ Plus[x_,y__]]:=c toSymbol[Plus[x,y]]/;NumericQ[c];
	toSymbol[Plus[x_,y__]]:=Plus@@Table[toSymbol[i],{i,List[x,y]}];
	toSymbol[c_ CircleDot[x__]]:=c toSymbol[CircleDot[x]]/;NumericQ[c];
	toSymbol[CircleDot[x_,y__]]:=Module[{functionWeights=Table[transcendentalWeight[List[x,y][[i]]],{i,Length@List[x,y]}]},CircleTimes@@Table[If[functionWeights[[i]]>=2,toSymbol[coproduct[{Floor[functionWeights[[i]]/2],Ceiling[functionWeights[[i]]/2]},List[x,y][[i]]]],symbol[List[x,y][[i]]]],{i,Length@List[x,y]}]];
)

defineSymbol;

(*defineCoproduct:=(
	ClearAll[coproduct,coproductReplacements];

	coproductReplacements={MPL[{0},x_]->Log[x],MPL[{1},x_]->Log[1-x],CircleTimes[x___,MPL[{0,0},y_],z___]->CircleTimes[x,Log[y]^2,z]/2,CircleTimes[x___,MPL[{1,1},1-y_],z___]->CircleTimes[x,Log[y]^2,z]/2,CircleTimes[x___,MPL[{0,0,0},y_],z___]->CircleTimes[x,Log[y]^3,z]/6,CircleTimes[x___,MPL[{1,1,1},1-y_],z___]->CircleTimes[x,Log[y]^3,z]/6,CircleTimes[x___,MPL[{0,0,0,0},y_],z___]->CircleTimes[x,Log[y]^4,z]/24,CircleTimes[x___,MPL[{1,1,1,1},1-y_],z___]->CircleTimes[x,Log[y]^4,z]/24,CircleTimes[x___,MPL[{0,0,0,0,0},y_],z___]->CircleTimes[x,Log[y]^5,z]/120,CircleTimes[x___,MPL[{1,1,1,1,1},1-y_],z___]->CircleTimes[x,Log[y]^5,z]/120,CircleTimes[x___,MPL[{0,0,0,0,0,0},y_],z___]->CircleTimes[x,Log[y]^6,z]/720,CircleTimes[x___,MPL[{1,1,1,1,1,1},1-y_],z___]->CircleTimes[x,Log[y]^6,z]/720,CircleTimes[x___,MPL[{0,0,0,0,0,0,0},y_],z___]->CircleTimes[x,Log[y]^7,z]/5040,CircleTimes[x___,MPL[{1,1,1,1,1,1,1},1-y_],z___]->CircleTimes[x,Log[y]^7,z]/5040,CircleTimes[x___,MPL[{0,0,0,0,0,0,0,0},y_],z___]->CircleTimes[x,Log[y]^8,z]/40320,CircleTimes[x___,MPL[{1,1,1,1,1,1,1,1},1-y_],z___]->CircleTimes[x,Log[y]^8,z]/40320,CircleTimes[x___,MPL[{0,0,0,0,0,0,0,0,0},y_],z___]->CircleTimes[x,Log[y]^9,z]/362880,CircleTimes[x___,MPL[{1,1,1,1,1,1,1,1,1},1-y_],z___]->CircleTimes[x,Log[y]^9,z]/362880};

	coproduct[weights_,MPL[a_,y_]]:=Print["Coproduct weights and function weight do not match"]/;Total[weights]!=Length[a];
	coproduct[weights_,PolyLog[n_,y_]]:=Print["Coproduct weights and function weight do not match"]/;Total[weights]!=n;
	coproduct[weights_,PolyLog[n_,y_]]:=If[First@weights==1,-1,1]CircleTimes@@Join[{PolyLog[First@weights,y]},Table[MPL[Table[1,{j,weights[[i]]}],1-y],{i,2,Length@weights}]]//.coproductReplacements;
	coproduct[weights_,MPL[a_,y_]]:=CircleTimes@@Table[MPL[Take[Reverse@a,{Total@Take[weights,i-1]+1,Total@Take[weights,i]}],y],{i,Length@weights}]//.coproductReplacements;)

defineCoproduct;*)

uniquePairs={{u,v},{u,w},{u,1-v},{u,1-w},{u,yu},{u,yv},{u,yw},{v,w},{v,1-u},{v,1-w},{v,yu},{v,yv},{v,yw},{w,1-u},{w,1-v},{w,yu},{w,yv},{w,yw},{1-u,1-v},{1-u,1-w},{1-u,yu},{1-u,yv},{1-u,yw},{1-v,1-w},{1-v,yu},{1-v,yv},{1-v,yw},{1-w,yu},{1-w,yv},{1-w,yw},{yu,yv},{yu,yw},{yv,yw}};

initializeFastExteriorD[w_]:=Block[{i,j,baseSymbols,fileExtention},
	ClearAll[t];
	fileExtention=If[imposeFirstEntryCondition==True,"]wfec.txt","].txt"];
	assignAntisymmetric[base_,pair_,var_]:=(fastExteriorDReplacement[base,pair[[1]],pair[[2]]]=t[var]; fastExteriorDReplacement[base,pair[[2]],pair[[1]]]=-t[var];);

	If[w<2,
		Print["Weight must be greater than 1"],
		For[i=1,i<=3,i++,
			fastExteriorDReplacement[s_,variables[[i]],variables[[i]]]=0; 
			fastExteriorDReplacement[s_,variables[[i]],1-variables[[i]]]=0; 
			fastExteriorDReplacement[s_,1-variables[[i]],variables[[i]]]=0; 
			fastExteriorDReplacement[s_,1-variables[[i]],1-variables[[i]]]=0;];
			fastExteriorDReplacement[s_,yu,yu] = fastExteriorDReplacement[s_,yv,yv] = fastExteriorDReplacement[s_,yw,yw] = 0;];
	
	If[w==2,
		For[i=1,i<=33,i++, 
		assignAntisymmetric[2,uniquePairs[[i]],i]];];
	If[w>2,
		baseSymbols=ReplaceAll[Get["~/Google\ Drive/Stanford/Lance/Mathematica\ Library/function_symbols/weight["<>ToString[w-2]<>fileExtention],{CircleTimes[DoubleBracketingBar[a__],b_]->CircleTimes[a,b]}];
		For[i=1,i<=Length@baseSymbols,i++,
			For[j=1,j<=33,j++,
				assignAntisymmetric[baseSymbols[[i]],uniquePairs[[j]],33(i-1)+j];
				basis[33(i-1)+j]=CircleTimes[DoubleBracketingBar[baseSymbols[[i]]],uniquePairs[[j,1]],uniquePairs[[j,2]]];]];];
	equationMultiplicity=33(i-2)+(j-1);

	currentWeight=w;
	ClearAll[assignAntisymmetric];
];

appendPreviousWeightSymbol[w_,convert_:False]:=Block[{i,j,lowerWeightSymbols,fileExtention},
	fileExtention=If[imposeFirstEntryCondition==True,"]wfec.txt","].txt"];
	lowerWeightSymbols=Get["~/Google\ Drive/Stanford/Lance/Mathematica\ Library/function_symbols/weight["<>ToString[w-1]<>fileExtention];
	If[convert==True,
		Flatten@Reap[For[i=1,i<=Length@lowerWeightSymbols,i++,
			For[j=1,j<=Length@middleEntries,j++,
				Sow[fastExteriorD[CircleTimes[lowerWeightSymbols[[i]],middleEntries[[j]]]]]];];][[2]],
		Flatten@Reap[For[i=1,i<=Length@lowerWeightSymbols,i++,
			For[j=1,j<=Length@middleEntries,j++,
				Sow[CircleTimes[lowerWeightSymbols[[i]],middleEntries[[j]]]]];];][[2]]]
];

setVariables[u];

countLyndonBasis[n_,alphabet_]:=Block[{m=Length[alphabet],d=Divisors@n},Plus@@(MoebiusMu[n/d]*m^d/n)] (*from Jeff*)

generateLyndonBasis[n_,alphabet_]:= Module[{w={alphabet[[1]]},i,temp,list={{alphabet[[1]]}},pos,j=1,k=0,max},
	max=Sum[countLyndonBasis[k,alphabet],{k,1,n}];
	Reap[
		Sow[w];
		For[j=1,j<max,j++,
			temp=PadRight[{},n,w];
			While[temp[[-1]]==alphabet[[-1]],temp=Drop[temp,-1]];
			pos=Flatten[Position[alphabet,temp[[-1]]]][[1]];
			temp[[-1]]=alphabet[[pos+1]];
			Sow[w=temp];];
][[2,1]]];(*from Jeff*)
