(* ::Package:: *)

ClearAll[cleanSolutions,singletReplacements,checkSinglets,identifyTriplets,threeCycleReplacements,threeCycleSingletReplacements,threeCycleKnownTripletReplacements,blockReplacementsOne,blockReplacementsTwo,blockReplacementsThree,checkThreeCycles]

cleanSolutions[newFunctions_,knownFunctions_]:=Module[{knownCoproducts,singlets,threeCycles,threeCycleImage,singletReplacementVector,updatedCyclicImage,resultingFunctions},
	knownCoproducts=coproduct[{transcendentalWeight[First[knownFunctions]]-1,1},#]&/@knownFunctions;
	Print["Anlyzing cyclic properties of inputs:"];
	cyclicImage=If[ValueQ[cyclicImage],cyclicImage,Monitor[Table[cyclicDecomposition[Join[newFunctions,knownCoproducts],m],{m,Length@newFunctions}],{m,Length@newFunctions}]];
	Print["All "<>ToString[Length@newFunctions]<>" inputs analyzed.\n"];
		singlets=DeleteCases[Table[If[IdentityMatrix[Length@newFunctions][[i]]==Take[cyclicImage[[i]],Length@newFunctions],i,Null],{i,Length@newFunctions}],Null];
		Print["Singlets identified as"];Print[singlets];
		Do[singletReplacementVector[i]=singletReplacements[cyclicImage[[i]],Length[knownFunctions]],{i,singlets}];
		resultingFunctions=ReplacePart[newFunctions,Table[i->Expand[newFunctions[[i]]+singletReplacementVector[i].knownCoproducts],{i,singlets}]];
		Print[checkSinglets[resultingFunctions,singlets]];
			threeCycles=identifyTriplets[cyclicImage,Length@newFunctions,singlets];
			Print["Three-cycles identified as"];Print[threeCycles];
			updatedCyclicImage=ReplacePart[cyclicImage,Table[j->cyclicImage[[j]]-Sum[cyclicImage[[j,i]]Join[ConstantArray[0,13],singletReplacementVector[i]],{i,singlets}],{j,Flatten[threeCycles]}]];
			resultingFunctions=ReplacePart[resultingFunctions,threeCycleReplacements[threeCycles,updatedCyclicImage,resultingFunctions,knownCoproducts,singlets]];
			Print[checkThreeCycles[resultingFunctions,threeCycles]];
				Print["Analyzing exchange properties of new functions:"];
				exchangeImage=Monitor[Table[exchangeDecomposition[Join[resultingFunctions,knownFunctions],u,v,m],{m,Length@resultingFunctions}],{m,Length@resultingFunctions}];
				Print["All "<>ToString[Length@resultingFunctions]<>" inputs analyzed.\n"];
					resultingFunctions=ReplacePart[resultingFunctions,exchangeReplacements[threeCycles,exchangeImage,resultingFunctions,knownCoproducts,Length[knownFunctions]]];
					Print["checkmark"];
					checkExchangePropertiesAndReorder[resultingFunctions,threeCycles,singlets]]

singletReplacements[noncyclicImage_,numberOfKnownFunctions_]:=Module[{replacementVector=ConstantArray[0,numberOfKnownFunctions],triplet},
	Do[triplet=Table[Take[noncyclicImage,-numberOfKnownFunctions][[j]],{j,3(i-1)+1,3i}];
		If[triplet!={0,0,0},
			If[Total[triplet]==0,
				replacementVector=ReplacePart[replacementVector,{3(i-1)+1->First[triplet],3(i-1)+2->-Last[triplet]}],
				Print["Nonstandard triplet found in cleanSinglet routine:"];Print[triplet]]]
			,{i,numberOfKnownFunctions/3}];
	replacementVector]

checkSinglets[functions_,singlets_]:=Module[{check},
	check=Table[Simplify[Expand[(functions[[j]]/.cycle)-functions[[j]]]]==0,{j,singlets}];
	If[And@@check,"All singlets clean and verified. \n","Unable to clean "<>ToString[Select[singlets,!check[[#]]&]]]]

identifyTriplets[fullImage_,numberOfFunctions_,knownSinglets_]:=Module[{remainingFunctions,image1,image2,image3,threeCycles={}},
	remainingFunctions=DeleteCases[Table[l,{l,numberOfFunctions}],Alternatives@@knownSinglets];
	While[remainingFunctions!={},
		image1=remainingFunctions[[Position[Table[fullImage[[First[remainingFunctions],l]],{l,remainingFunctions}],1][[1,1]]]];
		image2=remainingFunctions[[Position[Table[fullImage[[image1,l]],{l,remainingFunctions}],1][[1,1]]]];
		image3=remainingFunctions[[Position[Table[fullImage[[image2,l]],{l,remainingFunctions}],1][[1,1]]]];
		If[image3!=First[remainingFunctions],
			Print["Noncyclic triplet found"]; Print[First[remainingFunctions]->image1->image2->image3];,
			remainingFunctions=DeleteCases[remainingFunctions,Alternatives[image1,image2,image3]];AppendTo[threeCycles,{image3,image1,image2}]]];
	threeCycles]

threeCycleReplacements[threeCycles_,cyclicImage_,currentFunctions_,knownCoproducts_,singlets_]:=Module[{replacements={},threeCycleImage,currentFunctionReplacements,knownFunctionReplacements,numberOfSinglets=0},
	While[Simplify[Expand[(knownCoproducts[[Length@knownCoproducts-numberOfSinglets]]/.cycle)-knownCoproducts[[Length@knownCoproducts-numberOfSinglets]]]]==0,numberOfSinglets+=1];
	Do[threeCycleImage=Table[cyclicImage[[j]],{j,threeCycles[[i]]}];
		currentFunctionReplacements=threeCycleSingletReplacements[threeCycles[[i]],threeCycleImage,currentFunctions,singlets];
		knownFunctionReplacements=threeCycleKnownTripletReplacements[threeCycles[[i]],threeCycleImage,Length@knownCoproducts,numberOfSinglets];
		AppendTo[replacements,Table[threeCycles[[i,j]]->Expand[currentFunctions[[threeCycles[[i,j]]]]-currentFunctionReplacements[[j]].currentFunctions+knownFunctionReplacements[[j]].knownCoproducts],{j,3}]];
	,{i,Length[threeCycles]}];
	Flatten[replacements]]

threeCycleSingletReplacements[threeCycle_,threeCycleImage_,currentFunctions_,singlets_]:=
	Module[{replacementVectors=ConstantArray[0,{3,Length[currentFunctions]}](*offset={}*),singletImage,negativeEntries,positiveEntries,positivePosition,negativePosition},
		Do[singletImage=Table[threeCycleImage[[k,j]],{k,3}];
			If[singletImage!={0,0,0},
				negativeEntries=Select[singletImage,Negative[#]&];
				positiveEntries=Select[singletImage,Positive[#]&];
				If[Length[negativeEntries]==1\[And]Length[positiveEntries]==1,
					positivePosition=Position[singletImage,First[positiveEntries]][[1,1]];
					negativePosition=Position[singletImage,First[negativeEntries]][[1,1]];
					If[positivePosition==Mod[negativePosition-1,3,1],
						replacementVectors=ReplacePart[replacementVectors,{negativePosition,j}->First[negativeEntries]],
						If[positivePosition==Mod[negativePosition+1,3,1],
							replacementVectors=ReplacePart[replacementVectors,{positivePosition,j}->First[positiveEntries]],
							Print["Nonstandard singlet image found in threeCycleReplacements routine:"];Print[singletImage]]]];
				If[Length[negativeEntries]==2\[And]Length[positiveEntries]==1,
					If[Length[DeleteDuplicates[negativeEntries]]==1\[And]2 DeleteDuplicates[negativeEntries]==-positiveEntries,
						positivePosition=Position[singletImage,First[positiveEntries]][[1,1]];
						replacementVectors=ReplacePart[replacementVectors,{Mod[positivePosition+1,3,1],j}->2 First[negativeEntries]];
						replacementVectors=ReplacePart[replacementVectors,{Mod[positivePosition+2,3,1],j}->First[negativeEntries]],
						Print["Nonstandard singlet image found in threeCycleReplacements routine:"];Print[singletImage]]];
				If[Length[negativeEntries]==1\[And]Length[positiveEntries]==2,
					If[Length[DeleteDuplicates[positiveEntries]]==1\[And]2 DeleteDuplicates[positiveEntries]==-negativeEntries,
						negativePosition=Position[singletImage,First[negativeEntries]][[1,1]];
						replacementVectors=ReplacePart[replacementVectors,{Mod[negativePosition+1,3,1],j}->2 First[positiveEntries]];
						replacementVectors=ReplacePart[replacementVectors,{Mod[negativePosition+2,3,1],j}->First[positiveEntries]];,
						Print["Nonstandard singlet image found in threeCycleReplacements routine:"];Print[singletImage]]];
				If[Length[negativeEntries]==0\[Or]Length[positiveEntries]==0,Print["Nonstandard singlet image found in threeCycleReplacements routine:"];Print[singletImage]]];
		,{j,singlets}];
	replacementVectors]

threeCycleKnownTripletReplacements[threeCycle_,threeCycleImage_,numberOfKnownFunctions_,numberOfSinglets_]:=Module[{replacementVectors=ConstantArray[0,{3,numberOfKnownFunctions}],currentBlock,currentTriplet,numberOfNewFunctions},
	numberOfNewFunctions=Length[First[threeCycleImage]]-numberOfKnownFunctions;
	Do[currentBlock=Table[threeCycleImage[[All,k]],{k,numberOfNewFunctions+3(j-1)+1,numberOfNewFunctions+3j}]\[Transpose];
		If[currentBlock!={{0,0,0},{0,0,0},{0,0,0}},
			replacementVectors=ReplacePart[replacementVectors,Flatten[Table[{m,3(j-1)+n}->blockReplacementsOne[m,n,currentBlock],{m,3},{n,3}]]]]
		,{j,(numberOfKnownFunctions-numberOfSinglets)/3}];
	Do[currentTriplet=threeCycleImage[[All,numberOfNewFunctions+numberOfKnownFunctions-j]];
		If[currentTriplet!={0,0,0},
			replacementVectors=ReplacePart[replacementVectors,Table[{m,numberOfKnownFunctions-j}->tripletReplacementsTwo[m,currentTriplet],{m,3}]]]
		,{j,0,numberOfSinglets-1}];
	replacementVectors]

tripletReplacementsTwo[1,currentTriplet_]:=0;
tripletReplacementsTwo[2,currentTriplet_]:=currentTriplet[[1]];
tripletReplacementsTwo[3,currentTriplet_]:=-currentTriplet[[3]];

blockReplacementsOne[1,1,currentBlock_]:=-currentBlock[[1,1]]/2+currentBlock[[1,2]]/2-(3*currentBlock[[1,3]])/2-currentBlock[[2,1]]/2-(3*currentBlock[[2,2]])/2+currentBlock[[2,3]]/2+(3*currentBlock[[3,1]])/2-(3*currentBlock[[3,2]])/2-(3*currentBlock[[3,3]])/2;
blockReplacementsOne[1,2,currentBlock_]:=(-3*currentBlock[[1,1]])/2+(3*currentBlock[[1,2]])/2-(5*currentBlock[[1,3]])/2-currentBlock[[2,1]]/2-(5*currentBlock[[2,2]])/2+currentBlock[[2,3]]/2+(3*currentBlock[[3,1]])/2-(3*currentBlock[[3,2]])/2-(5*currentBlock[[3,3]])/2;
blockReplacementsOne[1,3,currentBlock_]:=0;
blockReplacementsOne[2,1,currentBlock_]:=-currentBlock[[1,1]]/2+currentBlock[[1,2]]/2-currentBlock[[1,3]]/2-currentBlock[[2,1]]/2-(3*currentBlock[[2,2]])/2+currentBlock[[2,3]]/2+currentBlock[[3,1]]/2-currentBlock[[3,2]]/2-(3*currentBlock[[3,3]])/2;
blockReplacementsOne[2,2,currentBlock_]:=(-3*currentBlock[[1,1]])/2+(3*currentBlock[[1,2]])/2-(3*currentBlock[[1,3]])/2-currentBlock[[2,1]]/2-(5*currentBlock[[2,2]])/2+currentBlock[[2,3]]/2+(3*currentBlock[[3,1]])/2-(3*currentBlock[[3,2]])/2-(5*currentBlock[[3,3]])/2;
blockReplacementsOne[2,3,currentBlock_]:=(-3*currentBlock[[1,1]])/2+(3*currentBlock[[1,2]])/2-(3*currentBlock[[1,3]])/2-currentBlock[[2,1]]/2-(5*currentBlock[[2,2]])/2+currentBlock[[2,3]]/2+(3*currentBlock[[3,1]])/2-(3*currentBlock[[3,2]])/2-(5*currentBlock[[3,3]])/2;
blockReplacementsOne[3,1,currentBlock_]:=-2*currentBlock[[1,1]]+2*currentBlock[[1,2]]-2*currentBlock[[1,3]]-3*currentBlock[[2,2]]+currentBlock[[2,3]]+2*currentBlock[[3,1]]-2*currentBlock[[3,2]]-3*currentBlock[[3,3]];
blockReplacementsOne[3,2,currentBlock_]:=-currentBlock[[1,1]]/2+currentBlock[[1,2]]/2-currentBlock[[1,3]]/2-currentBlock[[2,1]]/2-currentBlock[[2,2]]/2+currentBlock[[2,3]]/2+currentBlock[[3,1]]/2-currentBlock[[3,2]]/2-(3*currentBlock[[3,3]])/2;
blockReplacementsOne[3,3,currentBlock_]:=-currentBlock[[1,1]]+currentBlock[[1,2]]-currentBlock[[1,3]]-2*currentBlock[[2,2]]+currentBlock[[2,3]]+currentBlock[[3,1]]-currentBlock[[3,2]]-2*currentBlock[[3,3]];

checkThreeCycles[currentFunctions_,threeCycles_]:=Module[{check},
	check=Table[cyclicDecomposition[Table[currentFunctions[[j]],{j,threeCycles[[k]]}]]=={{0,1,0},{0,0,1},{1,0,0}},{k,Length@threeCycles}];
	If[TrueQ[And@@check],"All triplets clean and verified. \n","Unable to clean "<>ToString[Select[threeCycles,TrueQ[!check[[#]]]&]]]]

exchangeReplacements[threeCycles_,exchangeImage_,currentFunctions_,knownCoproducts_,numberOfKnownFunctions_]:=Module[{pairedTriplet,threeCycleImage,knownFunctionReplacements,replacements={}},
	pairedTriplet=Table[Floor[Position[exchangeDecomposition[knownCoproducts,u,v,m],1][[1,1]]/3]+1,{m,Table[-2+3i,{i,Length@knownCoproducts/3}]}];
	Monitor[Do[threeCycleImage=Table[exchangeImage[[j]],{j,threeCycles[[i]]}];
		knownFunctionReplacements=threeCycleExchangeReplacements[threeCycles[[i]],threeCycleImage,pairedTriplet,numberOfKnownFunctions];
		AppendTo[replacements,Table[threeCycles[[i,j]]->Expand[currentFunctions[[threeCycles[[i,j]]]]+knownFunctionReplacements[[j]].knownCoproducts],{j,3}]];
	,{i,Length[threeCycles]}],i]; 
	Flatten[replacements]]

threeCycleExchangeReplacements[threeCycle_,threeCycleImage_,tripletPairs_,numberOfKnownFunctions_]:=Module[{currentBlock,numberOfNewFunctions=Length[First[threeCycleImage]]-numberOfKnownFunctions,replacementVectors=ConstantArray[0,{3,numberOfKnownFunctions}],singlets,pairs},
	singlets=Select[Range[numberOfKnownFunctions/3],Position[tripletPairs,#][[1,1]]==#&];
	pairs=DeleteDuplicates[Table[Sort[{i,Position[tripletPairs,i][[1,1]]}],{i,DeleteCases[tripletPairs,Alternatives@@singlets]}]];
	Do[currentBlock=Table[threeCycleImage[[All,k]],{k,numberOfNewFunctions+3(j-1)+1,numberOfNewFunctions+3j}]\[Transpose];
		If[currentBlock!={{0,0,0},{0,0,0},{0,0,0}},replacementVectors=ReplacePart[replacementVectors,Flatten[Table[{m,3(j-1)+n}->blockReplacementsTwo[m,n,currentBlock],{m,3},{n,3}]]]]
	,{j,singlets}];
	Do[currentBlock=Table[threeCycleImage[[All,k]],{k,{numberOfNewFunctions+3(First[j]-1)+1,numberOfNewFunctions+3(First[j]-1)+2,numberOfNewFunctions+3(First[j]-1)+3,numberOfNewFunctions+3(Last[j]-1)+1,numberOfNewFunctions+3(Last[j]-1)+2,numberOfNewFunctions+3(Last[j]-1)+3}}]\[Transpose];
		If[currentBlock!={{0,0,0,0,0,0},{0,0,0,0,0,0},{0,0,0,0,0,0}},replacementVectors=ReplacePart[replacementVectors,Flatten[Table[{m,List[3(First[j]-1)+1,3(First[j]-1)+2,3(First[j]-1)+3,3(Last[j]-1)+1,3(Last[j]-1)+2,3(Last[j]-1)+3][[n]]}->blockReplacementsThree[m,n,currentBlock],{m,3},{n,6}]]]]
	,{j,pairs}];
	replacementVectors]

blockReplacementsTwo[1,1,currentBlock_]:=0;
blockReplacementsTwo[1,2,currentBlock_]:=currentBlock[[1,2]]/3-currentBlock[[1,3]]/3-(2*currentBlock[[2,1]])/3+(2*currentBlock[[2,2]])/3-currentBlock[[3,1]]/3-(2*currentBlock[[3,3]])/3;
blockReplacementsTwo[1,3,currentBlock_]:=currentBlock[[1,2]]-currentBlock[[1,3]]-currentBlock[[2,1]]+currentBlock[[2,2]]-currentBlock[[3,1]]-currentBlock[[3,3]];
blockReplacementsTwo[2,1,currentBlock_]:=currentBlock[[1,2]]-currentBlock[[1,3]]-currentBlock[[2,1]]+currentBlock[[2,2]]-currentBlock[[3,1]]-currentBlock[[3,3]];
blockReplacementsTwo[2,2,currentBlock_]:=0;
blockReplacementsTwo[2,3,currentBlock_]:=currentBlock[[1,2]]/3-currentBlock[[1,3]]/3-(2*currentBlock[[2,1]])/3+(2*currentBlock[[2,2]])/3-currentBlock[[3,1]]/3-(2*currentBlock[[3,3]])/3;
blockReplacementsTwo[3,1,currentBlock_]:=currentBlock[[1,2]]/3-currentBlock[[1,3]]/3-(2*currentBlock[[2,1]])/3+(2*currentBlock[[2,2]])/3-currentBlock[[3,1]]/3-(2*currentBlock[[3,3]])/3;
blockReplacementsTwo[3,2,currentBlock_]:=currentBlock[[1,2]]-currentBlock[[1,3]]-currentBlock[[2,1]]+currentBlock[[2,2]]-currentBlock[[3,1]]-currentBlock[[3,3]];
blockReplacementsTwo[3,3,currentBlock_]:=0;

blockReplacementsThree[1,1,currentBlock_]:=0;
blockReplacementsThree[1,2,currentBlock_]:=-currentBlock[[1, 1]] + currentBlock[[1, 3]] + currentBlock[[1, 5]] - currentBlock[[1, 6]] + 2*currentBlock[[2, 1]] - currentBlock[[2, 2]] - currentBlock[[2, 3]] - currentBlock[[2, 4]] + currentBlock[[2, 5]] + currentBlock[[3, 2]] - 3*currentBlock[[3, 3]] - currentBlock[[3, 4]] - currentBlock[[3, 6]];
blockReplacementsThree[1,3,currentBlock_]:=(2*currentBlock[[1,5]])/3-(2*currentBlock[[1,6]])/3-(2*currentBlock[[2,1]])/3+(2*currentBlock[[2,2]])/3-currentBlock[[2,4]]/3+currentBlock[[2,5]]/3-(2*currentBlock[[3,1]])/3-currentBlock[[3,3]]/3-(2*currentBlock[[3,4]])/3-currentBlock[[3,6]]/3;
blockReplacementsThree[1,4,currentBlock_]:=-currentBlock[[1,1]]+currentBlock[[1,3]]+(2*currentBlock[[1,5]])/3-(2*currentBlock[[1,6]])/3+(7*currentBlock[[2,1]])/3-(4*currentBlock[[2,2]])/3-currentBlock[[2,3]]-currentBlock[[2,4]]/3+currentBlock[[2,5]]/3+currentBlock[[3,1]]/3+currentBlock[[3,2]]-(10*currentBlock[[3,3]])/3-(2*currentBlock[[3,4]])/3-currentBlock[[3,6]]/3;
blockReplacementsThree[1,5,currentBlock_]:=-currentBlock[[3, 3]];
blockReplacementsThree[1,6,currentBlock_]:=-currentBlock[[1,1]]+currentBlock[[1,3]]+currentBlock[[1,5]]-currentBlock[[1,6]]+3*currentBlock[[2,1]]-2*currentBlock[[2,2]]-currentBlock[[2,3]]-currentBlock[[2,4]]+currentBlock[[2,5]]+currentBlock[[3,2]]-4*currentBlock[[3,3]]-currentBlock[[3,4]]-currentBlock[[3,6]];
blockReplacementsThree[2,1,currentBlock_]:=(2*currentBlock[[1,5]])/3-(2*currentBlock[[1,6]])/3-(2*currentBlock[[2,1]])/3+(2*currentBlock[[2,2]])/3-currentBlock[[2,4]]/3+currentBlock[[2,5]]/3-(2*currentBlock[[3,1]])/3-currentBlock[[3,3]]/3-(2*currentBlock[[3,4]])/3-currentBlock[[3,6]]/3;
blockReplacementsThree[2,2,currentBlock_]:=0;
blockReplacementsThree[2,3,currentBlock_]:=-currentBlock[[1,1]]+currentBlock[[1,3]]+currentBlock[[1,5]]-currentBlock[[1,6]]+2*currentBlock[[2,1]]-currentBlock[[2,2]]-currentBlock[[2,3]]-currentBlock[[2,4]]+currentBlock[[2,5]]+currentBlock[[3,2]]-3*currentBlock[[3,3]]-currentBlock[[3,4]]-currentBlock[[3,6]];
blockReplacementsThree[2,4,currentBlock_]:=-currentBlock[[1,1]]+currentBlock[[1,3]]+currentBlock[[1,5]]-currentBlock[[1,6]]+3*currentBlock[[2,1]]-2*currentBlock[[2,2]]-currentBlock[[2,3]]-currentBlock[[2,4]]+currentBlock[[2,5]]+currentBlock[[3,2]]-4*currentBlock[[3,3]]-currentBlock[[3,4]]-currentBlock[[3,6]];
blockReplacementsThree[2,5,currentBlock_]:=-currentBlock[[1,1]]+currentBlock[[1,3]]+(2*currentBlock[[1,5]])/3-(2*currentBlock[[1,6]])/3+(7*currentBlock[[2,1]])/3-(4*currentBlock[[2,2]])/3-currentBlock[[2,3]]-currentBlock[[2,4]]/3+currentBlock[[2,5]]/3+currentBlock[[3,1]]/3+currentBlock[[3,2]]-(10*currentBlock[[3,3]])/3-(2*currentBlock[[3,4]])/3-currentBlock[[3,6]]/3;
blockReplacementsThree[2,6,currentBlock_]:=-currentBlock[[3, 3]];
blockReplacementsThree[3,1,currentBlock_]:=-currentBlock[[1,1]]+currentBlock[[1,3]]+currentBlock[[1,5]]-currentBlock[[1,6]]+2*currentBlock[[2,1]]-currentBlock[[2,2]]-currentBlock[[2,3]]-currentBlock[[2,4]]+currentBlock[[2,5]]+currentBlock[[3,2]]-3*currentBlock[[3,3]]-currentBlock[[3,4]]-currentBlock[[3,6]];
blockReplacementsThree[3,2,currentBlock_]:=(2*currentBlock[[1,5]])/3-(2*currentBlock[[1,6]])/3-(2*currentBlock[[2,1]])/3+(2*currentBlock[[2,2]])/3-currentBlock[[2,4]]/3+currentBlock[[2,5]]/3-(2*currentBlock[[3,1]])/3-currentBlock[[3,3]]/3-(2*currentBlock[[3,4]])/3-currentBlock[[3,6]]/3;
blockReplacementsThree[3,3,currentBlock_]:=0;
blockReplacementsThree[3,4,currentBlock_]:=-currentBlock[[3, 3]];
blockReplacementsThree[3,5,currentBlock_]:=-currentBlock[[1,1]]+currentBlock[[1,3]]+currentBlock[[1,5]]-currentBlock[[1,6]]+3*currentBlock[[2,1]]-2*currentBlock[[2,2]]-currentBlock[[2,3]]-currentBlock[[2,4]]+currentBlock[[2,5]]+currentBlock[[3,2]]-4*currentBlock[[3,3]]-currentBlock[[3,4]]-currentBlock[[3,6]];
blockReplacementsThree[3,6,currentBlock_]:=-currentBlock[[1,1]]+currentBlock[[1,3]]+(2*currentBlock[[1,5]])/3-(2*currentBlock[[1,6]])/3+(7*currentBlock[[2,1]])/3-(4*currentBlock[[2,2]])/3-currentBlock[[2,3]]-currentBlock[[2,4]]/3+currentBlock[[2,5]]/3+currentBlock[[3,1]]/3+currentBlock[[3,2]]-(10*currentBlock[[3,3]])/3-(2*currentBlock[[3,4]])/3-currentBlock[[3,6]]/3;

checkExchangePropertiesAndReorder[currentFunctions_,threeCycles_,singlets_]:=Module[{checkSinglets,checkTriplets,uvExchangeImage,finalFunctions={}},
	uvExchangeImage=Table[exchangeDecomposition[Table[currentFunctions[[j]],{j,threeCycles[[k]]}],u,v],{k,Length@threeCycles}];
	checkSinglets=Table[exchangeDecomposition[currentFunctions[[k]],u,v],{k,singlets}];
	checkTriplets=Table[MatchQ[uvExchangeImage[[k]],Alternatives[{{0,1,0},{1,0,0},{0,0,1}},{{0,0,1},{0,1,0},{1,0,0}},{{1,0,0},{0,0,1},{0,1,0}}]],{k,Length@threeCycles}];
	If[TrueQ[And@@Join[checkSinglets,checkTriplets]],Print["All functions clean and verified."],Print["Unable to clean "<>ToString[Select[threeCycles,TrueQ[!Join[checkSinglets,checkTriplets][[#]]]&]]]];
	Do[Which[uvExchangeImage[[k]]=={{0,1,0},{1,0,0},{0,0,1}},AppendTo[finalFunctions,Table[currentFunctions[[j]],{j,threeCycles[[k]]}]],
			uvExchangeImage[[k]]=={{0,0,1},{0,1,0},{1,0,0}}, AppendTo[finalFunctions,Table[currentFunctions[[j]],{j,{(threeCycles[[k]])[[3]],(threeCycles[[k]])[[1]],(threeCycles[[k]])[[2]]}}]],
			uvExchangeImage[[k]]=={{1,0,0},{0,0,1},{0,1,0}}, AppendTo[finalFunctions,Table[currentFunctions[[j]],{j,{(threeCycles[[k]])[[2]],(threeCycles[[k]])[[3]],(threeCycles[[k]])[[1]]}}]]]
	,{k,Length@threeCycles}];
	Do[AppendTo[finalFunctions,currentFunctions[[k]]],{k,singlets}];
	Flatten[finalFunctions]]
