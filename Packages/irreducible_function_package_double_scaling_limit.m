(* ::Package:: *)

<<"angle_bracket_identities_double_scaling_limit.m"
stayInLyndonBasis=False;
variables={u,w,1-u,1-w,1-u-w};
uniquePairs={{u,w},{u,1-w},{u,1-u-w},{w,1-u},{w,1-u-w},{1-u,1-w},{1-u,1-u-w},{1-w,1-u-w}};

uwLinearBasisWeight[1]={MPL[{1}, 1 - u], MPL[{1}, 1 - w]};
uwLinearBasisWeight[weight_,normalize_:False]:=uwLinearBasisWeight[weight,normalize]=DeleteDuplicates[Join[Flatten@Table[{MPL[word,1-u],MPL[word,1-w]},{word,DeleteCases[Tuples[{0,1},weight],{___,0}]}],Flatten@MapThread[Flatten@Table[{MPL[word1,1-u]MPL[word2,1-w]/If[normalize,Sqrt[2],1],MPL[word1,1-w]MPL[word2,1-u]/If[normalize,Sqrt[2],1]},{word1,DeleteCases[Tuples[{0,1},#1],{___,0}]},{word2,DeleteCases[Tuples[{0,1},#2],{___,0}]}]&,IntegerPartitions[weight,{2}]\[Transpose]]]];
functionsWeight[n_]:=functionsWeight[n]=Join[uwLinearBasisWeight[n],Get["weight_"<>ToString[n]<>"_composite_double_scaling_functions_wfec.dat"],Get["weight_"<>ToString[n]<>"_irreducible_double_scaling_functions_wfec.dat"]];
beyondSymbolTerms[weight_,wfec_:True]:=Module[{functionsOfWeight,beyondSymbolFunctions},
	Do[functionsOfWeight[n]=functionsWeight[n],{n,weight-2}];
	beyondSymbolFunctions=Flatten[Table[Table[MZV[weight-n][[j]]functionsWeight[n][[k]],{k,Length[functionsWeight[n]]},{j,Length[MZV[weight-n]]}],{n,weight-2}]];
	Join[Reverse@beyondSymbolFunctions,MZV[weight]]];

loadFunctionsAndDefinitions[weight_]:=Block[{},
	currentWeightHPLs=uwLinearBasisWeight[weight];
	previousWeightHPLs=uwLinearBasisWeight[weight-1];
	previousPreviousWeightHPLs=uwLinearBasisWeight[weight-2];
	
	currentWeightCompositeFunctions=Get["weight_"<>ToString[weight]<>"_composite_double_scaling_functions_wfec.dat"];
	previousWeightCompositeFunctions=Get["weight_"<>ToString[weight-1]<>"_composite_double_scaling_functions_wfec.dat"];
	previousPreviousWeightCompositeFunctions=Get["weight_"<>ToString[weight-2]<>"_composite_double_scaling_functions_wfec.dat"];
	
	previousWeightIrreducibleFunctions=Get["weight_"<>ToString[weight-1]<>"_irreducible_double_scaling_functions_wfec.dat"];
	previousPreviousWeightIrreducibleFunctions=Get["weight_"<>ToString[weight-2]<>"_irreducible_double_scaling_functions_wfec.dat"];
	
	knownCurrentWeightFunctions=DeleteCases[Join[currentWeightHPLs,currentWeightCompositeFunctions,beyondSymbolTerms[currentWeight]],Alternatives@@MZV[currentWeight]];
	previousWeightFunctions=Join[previousWeightIrreducibleFunctions, previousWeightCompositeFunctions, previousWeightHPLs, beyondSymbolTerms[weight-1]];
	previousPreviousWeightFunctions=Join[previousPreviousWeightIrreducibleFunctions, previousPreviousWeightCompositeFunctions, previousPreviousWeightHPLs, beyondSymbolTerms[weight-2]];

	functions=Flatten@Table[t[i,AngleBracket@@j],{i,Length@previousPreviousWeightFunctions},{j,uniquePairs}];
	independentFunctions=Flatten@Table[t[i,AngleBracket@@j],{i,Length@previousPreviousWeightFunctions},{j,DeleteCases[uniquePairs,Alternatives@@{{1-u,1-u-w},{1-w,1-u-w}}]}];
	t[x_,Plus[y_,z__]]:=Plus@@Table[t[x,List[y,z][[i]]],{i,Length@List[y,z]}];
	t[x_,a_ \[LeftAngleBracket]y_,z_\[RightAngleBracket]]:=a t[x,\[LeftAngleBracket]y,z\[RightAngleBracket]]/;NumericQ[a];
	t[x_,0]:=0;
	previousWeightTerms=DeleteCases[previousWeightFunctions,Alternatives@@pureMZV];
	coefficients=Flatten@Table[a[l,m],{l,Length@previousWeightTerms},{m,variables}];
	allCoefficientsToZero=Table[coefficients[[i]]->0,{i,Length@coefficients}];];

GramSchmidt[vectors_]:=Monitor[Module[{v=ConstantArray[0,Length[vectors]]},
	Do[v[[n]]=vectors[[n]]-Sum[(v[[i]].vectors[[n]]/v[[i]].v[[i]])*v[[i]],{i,1,n-1}],{n,1,Length[vectors]}];
	v],{n,Length@vectors}];
getOrthogonalPart[vec_,basis_]:=Module[{overlap=basis.({vec}\[Transpose]),overlappingVectors,i,currentVector},
	If[overlap=={ConstantArray[0,Length@basis]},vec,
		overlappingVectors=Drop[ArrayRules[overlap]/.{Rule[{x_,1},c_]->x},-1];
		currentVector=vec;
		Do[currentVector -= Projection[currentVector,basis[[overlappingVectors[[i]]]]],{i,Length@overlappingVectors}];
		currentVector//Simplify]];

functionToVector[func_]:=functionToVectorBasis[Expand[func]];
functionToVectorBasis[0]:=ConstantArray[0,Length@coefficients];
functionToVectorBasis[Plus[func1_,funcN__]]:=Sum[functionToVector[i],{i,List[func1,funcN]}];
functionToVectorBasis[func_]:=functionToVectorBasis[coproduct[{currentWeight-1,1},func]]/;!MatchQ[func,CircleDot[__,_]]\[And]!MatchQ[func,Times[_,CircleDot[__,_]]];
functionToVectorBasis[func_]:=(func/.{CircleDot[x_,y_]:>a[Position[previousWeightFunctions,x][[1,1]],y]}/.{MPL[{0},x_]:>x,MPL[{1},x_]:>1-x}/.{a[i_,j_]:>ReplacePart[ConstantArray[0,Length@coefficients],Position[coefficients,a[i,j]][[1,1]]->1]})/;MatchQ[func,CircleDot[__,_]]\[Or]MatchQ[func,Times[_,CircleDot[__,_]]];
vectorToFunction[vec_]:=vec.coefficients/.{a[x_,y_]:>CircleDot[previousWeightFunctions[[x]],y/.{(1-u-w)->MPL[{0},1-u-w],(1-u)-> MPL[{0},1-u],(1-w)-> MPL[{0},1-w],u->MPL[{1},1-u],w->MPL[{1},1-w]}]};

cyclicDecomposition[functionBasis_]:= Block[{qArray=Array[q,Length@functionBasis],vectorBasis,replacements,m=1},
	Monitor[vectorBasis=qArray.(functionToVector/@functionBasis);
	Table[qArray/.(List@@Reduce[functionToVector[functionBasis[[m]]/.cycle]==vectorBasis]/.{Equal[x_,y_]:>Rule[x,y]}),{m,Length@functionBasis}],StringJoin[ToString[N[100(m-1)/Length[functionBasis],3]],"%"]]];
cyclicDecomposition[functionBasis_,functionImages_]:= Block[{qArray=Array[q,Length[functionBasis]+Length[functionImages]],allFuncs,vectorBasis,replacements,m=1},
	Monitor[allFuncs=Join[functionBasis,functionImages];
	vectorBasis=qArray.(functionToVector/@allFuncs);
	Table[qArray/.(List@@Reduce[functionToVector[functionBasis[[m]]/.cycle]==vectorBasis]/.{Equal[x_,y_]:>Rule[x,y]}),{m,Length@functionBasis}],StringJoin[ToString[N[100(m-1)/Length[functionBasis],3]],"%"]]]/;MatchQ[functionImages,List[__]];
cyclicDecomposition[functionBasis_,element_]:=Module[{replacements},
	replacements=List@@Reduce[functionToVector[functionBasis[[element]]/.cycle]==Array[q,Length@functionBasis].(functionToVector/@functionBasis),Array[q,Length@functionBasis]]/.{Equal[x_,y_]:>Rule[x,y]};
	Array[q,Length@functionBasis]/.replacements]/;!MatchQ[element,List[__]];

exchangeDecomposition[var1_,var2_,functionBasis_]:= Block[{qArray=Array[q,Length@functionBasis],vectorBasis,replacements,m=1},
	Monitor[vectorBasis=qArray.(functionToVector/@functionBasis);
	Table[qArray/.(List@@Reduce[functionToVector[functionBasis[[m]]/.exchange[var1,var2]]==vectorBasis]/.{Equal[x_,y_]:>Rule[x,y]}),{m,Length@functionBasis}],StringJoin[ToString[N[100(m-1)/Length[functionBasis],3]],"%"]]];
exchangeDecomposition[var1_,var2_,functionBasis_,functionImages_]:= Block[{qArray=Array[q,Length[functionBasis]+Length[functionImages]],allFuncs,vectorBasis,replacements,m=1},
	Monitor[allFuncs=Join[functionBasis,functionImages];
	vectorBasis=qArray.(functionToVector/@allFuncs);
	Table[qArray/.(List@@Reduce[functionToVector[functionBasis[[m]]/.exchange[var1,var2]]==vectorBasis]/.{Equal[x_,y_]:>Rule[x,y]}),{m,Length@functionBasis}],StringJoin[ToString[N[100(m-1)/Length[functionBasis],3]],"%"]]]/;MatchQ[functionImages,List[__]];
exchangeDecomposition[var1_,var2_,functionBasis_,element_]:=Module[{replacements},
	replacements=List@@Reduce[functionToVector[functionBasis[[element]]/.exchange[var1,var2]]==Array[q,Length@functionBasis].(functionToVector/@functionBasis),Array[q,Length@functionBasis]]/.{Equal[x_,y_]:>Rule[x,y]};
	Array[q,Length@functionBasis]/.replacements]/;!MatchQ[element,List[__]];

cyclicOrdering[inputBasis_,pos_:Null]:=Module[{singletPositions,originalOrder=Table[i,{i,2,Length@inputBasis+1}],cyclicOrder={1},cyclicImage=Table[Position[inputBasis,inputBasis[[i]]/.cycle][[1,1]],{i,Length@inputBasis}],k=1},
	singletPositions=Select[Range[Length@inputBasis],cyclicImage[[#]]==#&];
	originalOrder=DeleteCases[originalOrder,Alternatives@@singletPositions];
	While[k<=Length@inputBasis,
		If[!MemberQ[cyclicOrder,cyclicImage[[k]]],
			k=cyclicImage[[k]];AppendTo[cyclicOrder,k];originalOrder=DeleteCases[originalOrder,k],
			k=First[originalOrder];AppendTo[cyclicOrder,k];originalOrder=Drop[originalOrder,1]]];cyclicOrder=Join[DeleteCases[cyclicOrder,Length@inputBasis+1],singletPositions];
		Do[Which[
			(inputBasis[[cyclicOrder[[i]]]]/.exchange[u,v])===inputBasis[[cyclicOrder[[i]]]],cyclicOrder=ReplacePart[cyclicOrder,{i->cyclicOrder[[i+1]],i+1->cyclicOrder[[i+2]],i+2->cyclicOrder[[i]]}],
			(inputBasis[[cyclicOrder[[i]]]]/.exchange[u,v])===inputBasis[[cyclicOrder[[i+2]]]],cyclicOrder=ReplacePart[cyclicOrder,{i->cyclicOrder[[i+2]],i+1->cyclicOrder[[i]],i+2->cyclicOrder[[i+1]]}]]
			,{i,Table[3(j-1)+1,{j,(Length[inputBasis]-Length[singletPositions])/3}]}];
	If[pos===positions,cyclicOrder,Table[inputBasis[[i]],{i,cyclicOrder}]]];
