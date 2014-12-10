(* ::Package:: *)

<<angle_bracket_identities.m
LyndonBasis=True;
variables={u,v,w,1-u,1-v,1-w,yu,yv,yw};
uniquePairs={{u,v},{u,w},{u,1-v},{u,1-w},{u,yu},{u,yv},{u,yw},{v,w},{v,1-u},{v,1-w},{v,yu},{v,yv},{v,yw},{w,1-u},{w,1-v},{w,yu},{w,yv},{w,yw},{1-u,1-v},{1-u,1-w},{1-u,yu},{1-u,yv},{1-u,yw},{1-v,1-w},{1-v,yu},{1-v,yv},{1-v,yw},{1-w,yu},{1-w,yv},{1-w,yw},{yu,yv},{yu,yw},{yv,yw}};

loadFunctionsAndDefinitions[weight_]:=Block[{},
	currentWeightLyndonBasisFunctions=Get["weight_"<>ToString[weight]<>"_HPL_basis_wfec.dat"];
	previousWeightLyndonBasisFunctions=Get["weight_"<>ToString[weight-1]<>"_HPL_basis_wfec.dat"];
	previousPreviousWeightLyndonBasisFunctions=Get["weight_"<>ToString[weight-2]<>"_HPL_basis_wfec.dat"];
	
	currentWeightCompositeFunctions=If[2<weight\[And]basis===Lbasis,Get["weight_"<>ToString[weight]<>"_composite_basis_functions_wfec.dat"],Get["weight_"<>ToString[weight]<>"_composite_functions_wfec.dat"]];
	previousWeightCompositeFunctions=If[2<weight-1\[And]basis===Lbasis,Get["weight_"<>ToString[weight-1]<>"_composite_basis_functions_wfec.dat"],Get["weight_"<>ToString[weight-1]<>"_composite_functions_wfec.dat"]];
	previousPreviousWeightCompositeFunctions=If[2<weight-2\[And]basis===Lbasis,Get["weight_"<>ToString[weight-2]<>"_composite_basis_functions_wfec.dat"],Get["weight_"<>ToString[weight-2]<>"_composite_functions_wfec.dat"]];
	
	previousWeightIrreducibleFunctions=If[2<weight-1\[And]basis===Lbasis,Get["weight_"<>ToString[weight-1]<>"_irreducible_basis_functions_wfec.dat"],Get["weight_"<>ToString[weight-1]<>"_irreducible_functions_wfec.dat"]];
	previousPreviousWeightIrreducibleFunctions=If[2<weight-2\[And]basis===Lbasis,Get["weight_"<>ToString[weight-2]<>"_irreducible_basis_functions_wfec.dat"],Get["weight_"<>ToString[weight-2]<>"_irreducible_functions_wfec.dat"]];
	
	knownCurrentWeightFunctions=DeleteCases[Join[currentWeightLyndonBasisFunctions,currentWeightCompositeFunctions,beyondSymbolTerms[currentWeight](*,Flatten@Table[MZV[currentWeight-1][[i]]MPL[{0},j],{j,{1-u,1-v,1-w,yu,yv,yw}},{i,Length@MZV[currentWeight-1]}]*)],Alternatives@@MZV[currentWeight]];
	previousWeightFunctions=Join[previousWeightIrreducibleFunctions, previousWeightCompositeFunctions, previousWeightLyndonBasisFunctions, beyondSymbolTerms[weight-1]];
	previousPreviousWeightFunctions=Join[previousPreviousWeightIrreducibleFunctions, previousPreviousWeightCompositeFunctions, previousPreviousWeightLyndonBasisFunctions, beyondSymbolTerms[weight-2]];

	functions=Flatten@Table[t[i,AngleBracket@@j],{i,Length@previousPreviousWeightFunctions},{j,uniquePairs}];
	independentFunctions=Flatten@Table[t[i,AngleBracket@@j],{i,Length@previousPreviousWeightFunctions},{j,DeleteCases[uniquePairs,Alternatives@@{{u,v},{u,w},{v,w},{1-w,yw},{u,yv},{v,yw},{w,yu}}]}];
	t[x_,Plus[y_,z__]]:=Plus@@Table[t[x,List[y,z][[i]]],{i,Length@List[y,z]}];
	t[x_,a_ \[LeftAngleBracket]y_,z_\[RightAngleBracket]]:=a t[x,\[LeftAngleBracket]y,z\[RightAngleBracket]]/;NumericQ[a];
	t[x_,0]:=0;
	previousWeightTerms=DeleteCases[previousWeightFunctions,Alternatives@@pureMZV];
	(*coefficients=Flatten@Table[a[l,m],{l,Length@previousWeightTerms},{m,variables}];
	allCoefficientsToZero=Table[coefficients[[i]]->0,{i,Length@coefficients}];*)
	oddPreviousWeightTerms=Select[previousWeightTerms,OddQ[yGrading[#]]&];
	evenPreviousWeightTerms=Select[previousWeightTerms,EvenQ[yGrading[#]]&];
	oddCoefficients=Join[Flatten@Table[e[i,var],{i,Length@evenPreviousWeightTerms},{var,{yu,yv,yw}}],Flatten@Table[o[i,var],{i,Length@oddPreviousWeightTerms},{var,{u,v,w,1-u,1-v,1-w}}]];
	evenCoefficients=Join[Flatten@Table[o[i,var],{i,Length@oddPreviousWeightTerms},{var,{yu,yv,yw}}],Flatten@Table[e[i,var],{i,Length@evenPreviousWeightTerms},{var,{u,v,w,1-u,1-v,1-w}}]];];

GramSchmidt[vectors_]:=Monitor[Module[{v=ConstantArray[0,Length[vectors]]},
	Do[v[[n]]=vectors[[n]]-Sum[(v[[i]].vectors[[n]]/v[[i]].v[[i]])*v[[i]],{i,1,n-1}],{n,1,Length[vectors]}];
	v],{n,Length@vectors}];
getOrthogonalPart[vec_,basis_]:=Module[{overlap=basis.({vec}\[Transpose]),overlappingVectors,i,currentVector},
	If[overlap=={ConstantArray[0,Length@basis]},vec,
		overlappingVectors=Drop[ArrayRules[overlap]/.{Rule[{x_,1},c_]->x},-1];
		currentVector=vec;
		Do[currentVector -= Projection[currentVector,basis[[overlappingVectors[[i]]]]],{i,Length@overlappingVectors}];
		currentVector//Simplify]];

(*functionToVector[func_]:=functionToVectorBasis[Expand[func]];
functionToVectorBasis[0]:=ConstantArray[0,Length@coefficients];
functionToVectorBasis[Plus[func1_,funcN__]]:=Sum[functionToVector[i],{i,List[func1,funcN]}];
functionToVectorBasis[func_]:=functionToVectorBasis[coproduct[{currentWeight-1,1},func]]/;!MatchQ[func,CircleDot[__,_]]\[And]!MatchQ[func,Times[_,CircleDot[__,_]]];
functionToVectorBasis[func_]:=(func/.{CircleDot[x_,y_]:>a[Position[previousWeightFunctions,x][[1,1]],y]}/.{MPL[{0},x_]:>x,MPL[{1},x_]:>1-x}/.{a[i_,j_]:>ReplacePart[ConstantArray[0,Length@coefficients],Position[coefficients,a[i,j]][[1,1]]->1]})/;MatchQ[func,CircleDot[__,_]]\[Or]MatchQ[func,Times[_,CircleDot[__,_]]];
vectorToFunction[vec_]:=vec.coefficients/.{a[x_,y_]:>CircleDot[previousWeightFunctions[[x]],y/.{1-u->MPL[{0},1-u],1-v->MPL[{0},1-v],1-w->MPL[{0},1-w],u->MPL[{1},1-u],v->MPL[{1},1-v],w->MPL[{1},1-w],yu->MPL[{0},yu],yv->MPL[{0},yv],yw->MPL[{0},yw]}]};*)
functionToVector[func_]:=functionToEvenVectorBasis[Expand[func]]/;EvenQ[yGrading[func]];
functionToVector[func_]:=functionToOddVectorBasis[Expand[func]]/;OddQ[yGrading[func]];
functionToEvenVectorBasis[0]:=ConstantArray[0,Length@coefficients];
functionToOddVectorBasis[0]:=ConstantArray[0,Length@coefficients];
functionToEvenVectorBasis[Plus[func1_,funcN__]]:=Sum[functionToVector[i],{i,List[func1,funcN]}];
functionToOddVectorBasis[Plus[func1_,funcN__]]:=Sum[functionToVector[i],{i,List[func1,funcN]}];
functionToEvenVectorBasis[func_]:=functionToEvenVectorBasis[coproduct[{currentWeight-1,1},func]]/;!MatchQ[func,CircleDot[__,_]]\[And]!MatchQ[func,Times[_,CircleDot[__,_]]];
functionToOddVectorBasis[func_]:=functionToOddVectorBasis[coproduct[{currentWeight-1,1},func]]/;!MatchQ[func,CircleDot[__,_]]\[And]!MatchQ[func,Times[_,CircleDot[__,_]]]
functionToEvenVectorBasis[func_]:=(func/.{CircleDot[x_,y_]:>e[Position[evenPreviousWeightTerms,x][[1,1]],y]/;EvenQ[yGrading[x]],CircleDot[x_,y_]:>o[Position[oddPreviousWeightTerms,x][[1,1]],y]/;OddQ[yGrading[x]]}/.{MPL[{0},x_]:>x,MPL[{1},x_]:>1-x}/.{e[i_,j_]:>ReplacePart[ConstantArray[0,Length@evenCoefficients],Position[evenCoefficients,e[i,j]][[1,1]]->1],o[i_,j_]:>ReplacePart[ConstantArray[0,Length@evenCoefficients],Position[evenCoefficients,o[i,j]][[1,1]]->1]})/;MatchQ[func,CircleDot[__,_]]\[Or]MatchQ[func,Times[_,CircleDot[__,_]]];
functionToOddVectorBasis[func_]:=(func/.{CircleDot[x_,y_]:>o[Position[oddPreviousWeightTerms,x][[1,1]],y]/;OddQ[yGrading[x]],CircleDot[x_,y_]:>e[Position[evenPreviousWeightTerms,x][[1,1]],y]/;EvenQ[yGrading[x]]}/.{MPL[{0},x_]:>x,MPL[{1},x_]:>1-x}/.{o[i_,j_]:>ReplacePart[ConstantArray[0,Length@oddCoefficients],Position[oddCoefficients,o[i,j]][[1,1]]->1],e[i_,j_]:>ReplacePart[ConstantArray[0,Length@oddCoefficients],Position[oddCoefficients,e[i,j]][[1,1]]->1]})/;MatchQ[func,CircleDot[__,_]]\[Or]MatchQ[func,Times[_,CircleDot[__,_]]];

toCoefficients[func_]:=toEvenCoefficients[Expand[func]]/;EvenQ[yGrading[func]];
toCoefficients[func_]:=toOddCoefficients[Expand[func]]/;OddQ[yGrading[func]];
toEvenCoefficients[Plus[func1_,funcN__]]:=Sum[toEvenCoefficients[i],{i,List[func1,funcN]}];
toOddCoefficients[Plus[func1_,funcN__]]:=Sum[toOddCoefficients[i],{i,List[func1,funcN]}];
toEvenCoefficients[func_]:=toEvenCoefficients[coproduct[{currentWeight-1,1},func]]/;!MatchQ[func,CircleDot[__,_]]\[And]!MatchQ[func,Times[_,CircleDot[__,_]]]\[And]!MatchQ[func,Plus[_,__]];
toOddCoefficients[func_]:=toOddCoefficients[coproduct[{currentWeight-1,1},func]]/;!MatchQ[func,CircleDot[__,_]]\[And]!MatchQ[func,Times[_,CircleDot[__,_]]]\[And]!MatchQ[func,Plus[_,__]];
toEvenCoefficients[func_]:=(func/.{CircleDot[x_,y_]:>e[Position[evenPreviousWeightTerms,x][[1,1]],y]/;EvenQ[yGrading[x]],CircleDot[x_,y_]:>o[Position[oddPreviousWeightTerms,x][[1,1]],y]/;OddQ[yGrading[x]]})/;MatchQ[func,CircleDot[__,_]]\[Or]MatchQ[func,Times[_,CircleDot[__,_]]];
toOddCoefficients[func_]:=(func/.{CircleDot[x_,y_]:>o[Position[oddPreviousWeightTerms,x][[1,1]],y]/;OddQ[yGrading[x]],CircleDot[x_,y_]:>e[Position[evenPreviousWeightTerms,x][[1,1]],y]/;EvenQ[yGrading[x]]})/;MatchQ[func,CircleDot[__,_]]\[Or]MatchQ[func,Times[_,CircleDot[__,_]]];

(*cyclicDecomposition[functionBasis_]:= Monitor[Table[cyclicDecomposition[functionBasis,m],{m,Length@functionBasis}],StringJoin[ToString[N[100(m-1)/Length[functionBasis],3]],"%"]];*)
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

(*exchangeDecomposition[functionBasis_,var1_,var2_]:=Monitor[Table[exchangeDecomposition[functionBasis,var1,var2,m],{m,Length@functionBasis}],StringJoin[ToString[N[100(m-1)/Length[functionBasis],3]],"%"]];
exchangeDecomposition[functionBasis_,var1_,var2_,element_]:=Module[{replacements},
	replacements=List@@Reduce[functionToVector[functionBasis[[element]]/.exchange[var1,var2]]==Array[q,Length@functionBasis].(functionToVector/@functionBasis),Array[q,Length@functionBasis]]/.{Equal[x_,y_]:>Rule[x,y]};
	If[!TrueQ[!replacements],Array[q,Length@functionBasis]/.replacements,Print["No solution found for function "<>ToString[element]];ConstantArray[z,Length[functionBasis]]]];*)
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
	originalOrder=DeleteCases[originalOrder,Alternatives@@(singletPositions+1)];
	While[k<=Length@inputBasis,
		If[!MemberQ[cyclicOrder,cyclicImage[[k]]],
			k=cyclicImage[[k]];AppendTo[cyclicOrder,k];originalOrder=DeleteCases[originalOrder,k],
			k=First[originalOrder];AppendTo[cyclicOrder,k];originalOrder=Drop[originalOrder,1]]];cyclicOrder=Join[DeleteCases[cyclicOrder,Length@inputBasis+1],singletPositions];
		Do[Which[
			(inputBasis[[cyclicOrder[[i]]]]/.exchange[u,v])===inputBasis[[cyclicOrder[[i]]]],cyclicOrder=ReplacePart[cyclicOrder,{i->cyclicOrder[[i+1]],i+1->cyclicOrder[[i+2]],i+2->cyclicOrder[[i]]}],
			(inputBasis[[cyclicOrder[[i]]]]/.exchange[u,v])===inputBasis[[cyclicOrder[[i+2]]]],cyclicOrder=ReplacePart[cyclicOrder,{i->cyclicOrder[[i+2]],i+1->cyclicOrder[[i]],i+2->cyclicOrder[[i+1]]}]]
			,{i,Table[3(j-1)+1,{j,(Length[inputBasis]-Length[singletPositions])/3}]}];
	If[pos===positions,cyclicOrder,Table[inputBasis[[i]],{i,cyclicOrder}]]];

exchangeOrdering[functions_]:=Module[{newOrdering,permutationImages,sixCycles={},threeCycles={},singlets={}},
	Do[If[!MemberQ[Flatten@Join[sixCycles,threeCycles,singlets],functions[[i]]],permutationImages=DeleteDuplicates[{functions[[i]],functions[[i]]/.cycle,functions[[i]]/.cycle/.cycle,functions[[i]]/.exchange[v,w],functions[[i]]/.exchange[u,v],functions[[i]]/.exchange[u,w]}];
		Which[
			Length[permutationImages]==6,AppendTo[sixCycles,permutationImages],
			Length[permutationImages]==3,Which[
				(permutationImages[[1]]/.exchange[u,v])==permutationImages[[1]],AppendTo[threeCycles,Table[permutationImages[[i]],{i,{2,3,1}}]],
				(permutationImages[[1]]/.exchange[u,v])==permutationImages[[2]],AppendTo[threeCycles,Table[permutationImages[[i]],{i,{1,2,3}}]],
				(permutationImages[[1]]/.exchange[u,v])==permutationImages[[3]],AppendTo[threeCycles,Table[permutationImages[[i]],{i,{3,1,2}}]]],
			Length[permutationImages]==1,AppendTo[singlets,permutationImages]]]
	,{i,Length@functions}];
	numberOfSixCycles=Length[sixCycles];
	numberOfThreeCycles=Length[threeCycles];
	numberOfSinglets=Length[singlets];
	Join[Flatten@sixCycles,Flatten@threeCycles,Flatten@singlets]];
