(* ::Package:: *)

<<"angle_bracket_identities_spurious_pole_surface.m"
LyndonBasis=True;
variables={u,v,1-u,1-v,u-v};
uniquePairs={{u, v}, {u, 1 - v}, {v, 1 - u}, {1 - u, 1 - v}, {u, u - v}, {v, u - v}, {1 - u, u - v}, {1 - v, u - v}};

ClearAll[beyondSymbolTerms]
uvLinearBasisWeight[1]={MPL[{1}, 1 - u], MPL[{1}, 1 - v]};
uvLinearBasisWeight[weight_]:=(uvLinearBasisWeight[weight]=DeleteDuplicates[Join[Flatten@Table[{MPL[word,1-u],MPL[word,1-v]},{word,Select[generateLyndonBasis[weight,{0,1}],Length[#]==weight&]}],Flatten@Table[Flatten@Table[f1 f2,{f1,uvLinearBasisWeight[ii]},{f2,uvLinearBasisWeight[weight-ii]}],{ii,weight-1}]]])/;weight>1;
functionsWeight[n_]:=functionsWeight[n]=Join[uvLinearBasisWeight[n],Get["weight_"<>ToString[n]<>"_composite_spurious_pole_surface_functions.dat"],Get["weight_"<>ToString[n]<>"_irreducible_spurious_pole_surface_functions.dat"]];
beyondSymbolTerms[weight_,wfec_:True]:=Module[{functionsOfWeight,beyondSymbolFunctions},
	Do[functionsOfWeight[n]=functionsWeight[n],{n,weight-2}];
	beyondSymbolFunctions=Flatten[Table[Table[MZV[weight-n][[j]]functionsWeight[n][[k]],{k,Length[functionsWeight[n]]},{j,Length[MZV[weight-n]]}],{n,weight-2}]];
	Join[Reverse@beyondSymbolFunctions,MZV[weight]]];

loadFunctionsAndDefinitions[weight_]:=Block[{},
	currentWeightLyndonBasisFunctions=uvLinearBasisWeight[weight];
	previousWeightLyndonBasisFunctions=uvLinearBasisWeight[weight-1];
	previousPreviousWeightLyndonBasisFunctions=uvLinearBasisWeight[weight-2];
	
	currentWeightCompositeFunctions=Get["weight_"<>ToString[weight]<>"_composite_spurious_pole_surface_functions.dat"];
	previousWeightCompositeFunctions=Get["weight_"<>ToString[weight-1]<>"_composite_spurious_pole_surface_functions.dat"];
	previousPreviousWeightCompositeFunctions=Get["weight_"<>ToString[weight-2]<>"_composite_spurious_pole_surface_functions.dat"];

	previousWeightIrreducibleFunctions=Get["weight_"<>ToString[weight-1]<>"_irreducible_spurious_pole_surface_functions.dat"];
	previousPreviousWeightIrreducibleFunctions=Get["weight_"<>ToString[weight-2]<>"_irreducible_spurious_pole_surface_functions.dat"];

	knownCurrentWeightFunctions=DeleteCases[Join[currentWeightLyndonBasisFunctions,currentWeightCompositeFunctions,beyondSymbolTerms[currentWeight]],Alternatives@@MZV[currentWeight]];
	previousWeightFunctions=Join[previousWeightIrreducibleFunctions, previousWeightCompositeFunctions, previousWeightLyndonBasisFunctions, beyondSymbolTerms[weight-1]];
	previousPreviousWeightFunctions=Join[previousPreviousWeightIrreducibleFunctions, previousPreviousWeightCompositeFunctions, previousPreviousWeightLyndonBasisFunctions, beyondSymbolTerms[weight-2]];

	functions=Flatten@Table[t[i,AngleBracket@@j],{i,Length@previousPreviousWeightFunctions},{j,uniquePairs}];
	independentFunctions=Flatten@Table[t[i,AngleBracket@@j],{i,Length@previousPreviousWeightFunctions},{j,DeleteCases[uniquePairs,Alternatives@@{{u,u-v},{1-u,1-v}}]}];
	t[x_,Plus[y_,z__]]:=Plus@@Table[t[x,List[y,z][[i]]],{i,Length@List[y,z]}];
	t[x_,a_ \[LeftAngleBracket]y_,z_\[RightAngleBracket]]:=a t[x,\[LeftAngleBracket]y,z\[RightAngleBracket]]/;NumericQ[a];
	t[x_,0]:=0;
	previousWeightTerms=DeleteCases[previousWeightFunctions,Alternatives@@pureMZV];
	coefficients=Flatten@Table[a[l,m],{l,Length@previousWeightTerms},{m,variables}];
	allCoefficientsToZero=Table[coefficients[[i]]->0,{i,Length@coefficients}]];
	
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
vectorToFunction[vec_]:=vec.coefficients/.{a[x_,y_]:>CircleDot[previousWeightFunctions[[x]],y/.{1-u->MPL[{0},1-u],1-v->MPL[{0},1-v],u->MPL[{1},1-u],v->MPL[{1},1-v],u-v->MPL[{0},u-v]}]};
