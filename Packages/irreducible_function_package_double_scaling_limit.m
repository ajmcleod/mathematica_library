(* ::Package:: *)

<<"angle_bracket_identities_double_scaling_limit.m"
stayInLyndonBasis=True;
variables={1-u-w,1-u,1-w,u,w};
uniquePairs={{u,w},{u,1-w},{u,1-u-w},{w,1-u},{w,1-u-w},{1-u,1-w},{1-u,1-u-w},{1-w,1-u-w}};
sortedFunctionsWeightDS[weight_]:=sortedFunctionsWeightDS[weight]=Sort[functionsWeight[DS,weight]];

loadFunctionsAndDefinitions[weight_]:=Block[{},
	currentWeightLyndonBasisFunctions=Get[$MathematicaLibrary<>"/Function Library/Weight "<>ToString[weight]<>"/weight_"<>ToString[weight]<>"_HPL_DS_basis.dat"];	
	currentWeightCompositeFunctions=Get[$MathematicaLibrary<>"/Function Library/Weight "<>ToString[weight]<>"/weight_"<>ToString[weight]<>"_composite_DS_functions.dat"];
	
    knownCurrentWeightFunctions=DeleteCases[Join[currentWeightCompositeFunctions,currentWeightLyndonBasisFunctions,beyondSymbolTerms[DS,weight]],Alternatives@@MZV[currentWeight]];
	previousWeightFunctions=sortedFunctionsWeightDS[weight-1];
	previousPreviousWeightFunctions=sortedFunctionsWeightDS[weight-2];

	functions=Flatten@Table[t[i,AngleBracket@@j],{i,Length@previousPreviousWeightFunctions},{j,uniquePairs}];
	independentFunctions=Flatten@Table[t[i,AngleBracket@@j],{i,Length@previousPreviousWeightFunctions},{j,DeleteCases[uniquePairs,Alternatives@@{{1-u,1-u-w},{1-w,1-u-w}}]}];
	t[x_,Plus[y_,z__]]:=Plus@@Table[t[x,List[y,z][[i]]],{i,Length@List[y,z]}];
	t[x_,a_ \[LeftAngleBracket]y_,z_\[RightAngleBracket]]:=a t[x,\[LeftAngleBracket]y,z\[RightAngleBracket]]/;NumericQ[a];
	t[x_,0]:=0;

    previousWeightTerms=DeleteCases[previousWeightFunctions,Alternatives@@pureMZV];
	coefficients=Flatten@Table[a[l,m],{l,Length@previousWeightTerms},{m,variables}]];

functionToVector[func_]:=functionToVectorBasis[Expand[func]];
functionToVectorBasis[0]:=ConstantArray[0,Length@coefficients];
functionToVectorBasis[func_]:=Module[{sparse=CoefficientArrays[toCoefficients[Expand[func]],coefficients]}, If[sparse[[1]]!=0,Print["Function could not be converted to vector because of these terms: "<>ToString[sparse[[1]]]]]; Normal[sparse[[2]]]];

vectorToFunction[vec_]:=vec.coefficients/.{a[x_,y_]:>CircleDot[previousWeightTerms[[x]],Log[y]]};
toCoefficients[Plus[func1_,funcN__]]:=Sum[toCoefficients[i],{i,List[func1,funcN]}];
toCoefficients[func_]:=toCoefficients[coproduct[{currentWeight-1,1},func]]/;!MatchQ[func,CircleDot[__,_]]\[And]!MatchQ[func,Times[_,CircleDot[__,_]]]\[And]!MatchQ[func,Plus[_,__]];
toCoefficients[func_]:=(func/.{CircleDot[x_,y_]:>a[Position[previousWeightTerms,x][[1,1]],y]}/.toLogs/.Log[y_]:>y)/;MatchQ[func,CircleDot[__,_]]\[Or]MatchQ[func,Times[_,CircleDot[__,_]]];
