(* ::Package:: *)

hexagonSymbolLevelFunctionsWeight[weight_]:=hexagonSymbolLevelFunctionsWeight[weight]=Join[Array[Symbol["E"<>ToString[weight]],numFuncs[Symbol["E"<>ToString[weight]]]],Array[Symbol["O"<>ToString[weight]],numFuncs[Symbol["O"<>ToString[weight]]]],HPLbasisHexagon[weight],compositeFuncsHexagon[weight]];
hexagonBeyondSymbolTerms[weight_]:=hexagonBeyondSymbolTerms[weight]=Module[{beyondSymbolFunctions},beyondSymbolFunctions=Flatten[Table[Table[MZV[weight-n][[j]]hexagonSymbolLevelFunctionsWeight[n][[k]],{k,Length[hexagonSymbolLevelFunctionsWeight[n]]},{j,Length[MZV[weight-n]]}],{n,weight-2}]]; Join[Reverse@beyondSymbolFunctions,MZV[weight]]];
hexagonFunctionsWeight[weight_]:=hexagonFunctionsWeight[weight]=Join[hexagonSymbolLevelFunctionsWeight[weight],hexagonBeyondSymbolTerms[weight]];

dsHeptagonArguments = {{u1*u4, u2*u6}, {u2*u5, u3*u7}, {u3*u6, u1*u4}, {u4*u7, u2*u5}, {u1*u5, u3*u6}, {u2*u6, u4*u7}, {u3*u7, u1*u5}, {u2*u6, u1*u4}, {u3*u7, u2*u5}, {u1*u4, u3*u6}, {u2*u5, u4*u7}, {u3*u6, u1*u5}, {u4*u7, u2*u6}, {u1*u5, u3*u7}};
dtHeptagonArguments = {{u4,u7},{u1,u5},{u2,u6},{u3,u7},{u1,u4},{u2,u5},{u3,u6},{u7,u4},{u5,u1},{u6,u2},{u7,u3},{u4,u1},{u5,u2},{u6,u3}};
heptagonSymbolLevelFunctionsWeight[weight_]:=heptagonSymbolLevelFunctionsWeight[weight]=Join[Array[Symbol["\[CapitalEpsilon]"<>ToString[weight]],numFuncs[Symbol["\[CapitalEpsilon]"<>ToString[weight]]]],Array[Symbol["\[CapitalOmicron]"<>ToString[weight]],numFuncs[Symbol["\[CapitalOmicron]"<>ToString[weight]]]],DeleteDuplicates[Flatten[Table[Symbol["ds"<>ToString[weight]][ii]@@@dsHeptagonArguments,{ii,numFuncs[Symbol["ds"<>ToString[weight]]]}]]],DeleteDuplicates[Flatten[Table[Symbol["dt"<>ToString[weight]][ii]@@@dtHeptagonArguments,{ii,numFuncs[Symbol["dt"<>ToString[weight]]]}]]/.{-dt4[ii_][a_,b_]:>dt4[ii][a,b],-dt6[ii_][a_,b_]:>dt6[ii][a,b],-dt7[ii_][a_,b_]:>dt7[ii][a,b],-dt8[ii_][a_,b_]:>dt8[ii][a,b]}],HPLbasisHeptagon[weight],compositeFuncsHeptagon[weight]];
heptagonBeyondSymbolTerms[weight_]:=heptagonBeyondSymbolTerms[weight]=Module[{beyondSymbolFunctions},beyondSymbolFunctions=Flatten[Table[Table[MZV[weight-n][[j]]heptagonSymbolLevelFunctionsWeight[n][[k]],{k,Length[heptagonSymbolLevelFunctionsWeight[n]]},{j,Length[MZV[weight-n]]}],{n,weight-2}]]; Join[Reverse@beyondSymbolFunctions,MZV[weight]]];
heptagonFunctionsWeight[weight_]:=heptagonFunctionsWeight[weight]=Join[heptagonSymbolLevelFunctionsWeight[weight],heptagonBeyondSymbolTerms[weight]];

symbolLevelFunctions[funcType_,weight_]:=symbolLevelFunctions[funcType,weight]=Join[Symbol["HPLbasis"<>ToString[funcType]][weight],Symbol["compositeFuncs"<>ToString[funcType]][weight],Array[Symbol[ToString[funcType]<>ToString[weight]],numFuncs[Symbol[ToString[funcType]<>ToString[weight]]]]];
beyondSymbolTerms[funcType_,weight_]:=beyondSymbolTerms[funcType,weight]=Module[{beyondSymbolFunctions},beyondSymbolFunctions=Flatten[Table[Table[MZV[weight-n][[j]]symbolLevelFunctions[funcType,n][[k]],{k,Length[symbolLevelFunctions[funcType,n]]},{j,Length[MZV[weight-n]]}],{n,weight-2}]]; Join[Reverse@beyondSymbolFunctions,MZV[weight]]];
functionsWeight[funcType_,weight_]:=functionsWeight[funcType,weight]=Join[symbolLevelFunctions[funcType,weight],beyondSymbolTerms[funcType,weight]];

HPLbasisHexagon[weight_]:=Module[{},HPLbasisHexagon[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Base Code/Local Binaries/HPLbasisHexagon_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["HPL basis of Hexagon Functions loaded"]];
  HPLbasisHexagon[weight]];
HPLbasisHeptagon[weight_]:=Module[{},HPLbasisHeptagon[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Base Code/Local Binaries/HPLbasisHeptagon_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["HPL basis of Heptagon Functions loaded"]];
  HPLbasisHeptagon[weight]];
HPLbasisDS[weight_]:=Module[{},HPLbasisDS[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Base Code/Local Binaries/HPLbasisDS_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["HPL basis of DS functions loaded"]];
  HPLbasisDS[weight]];
HPLbasisDT[weight_]:=Module[{},HPLbasisDT[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Base Code/Local Binaries/HPLbasisDT_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["HPL basis of DT functions loaded"]];
  HPLbasisDT[weight]];
HPLbasisSP[weight_]:=Module[{},HPLbasisSP[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Base Code/Local Binaries/HPLbasisSP_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["HPL basis of SP functions loaded"]];
  HPLbasisSP[weight]];

compositeFuncsHexagon[weight_]:=Module[{},compositeFuncsHexagon[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Base Code/Local Binaries/compositeFuncsHexagon_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["composite Hexagon functions loaded"]];
  compositeFuncsHexagon[weight]];
compositeFuncsHeptagon[weight_]:=Module[{},compositeFuncsHeptagon[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Base Code/Local Binaries/compositeFuncsHeptagon_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["composite Heptagon functions loaded"]];
  compositeFuncsHeptagon[weight]];
compositeFuncsDS[weight_]:=Module[{},compositeFuncsDS[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Base Code/Local Binaries/compositeFuncsDS_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["composite DS functions loaded"]];
  compositeFuncsDS[weight]];
compositeFuncsDT[weight_]:=Module[{},compositeFuncsDT[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Base Code/Local Binaries/compositeFuncsDT_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["composite DT functions loaded"]];
  compositeFuncsDT[weight]];
compositeFuncsSP[weight_]:=Module[{},compositeFuncsSP[temp_]=.;
  Get[$MathematicaLibrary<>"/Function Library/Base Code/Local Binaries/compositeFuncsSP_"<>ToString[Floor[$VersionNumber]]<>".mx"];
  If[debug,Print["composite SP functions loaded"]];
  compositeFuncsSP[weight]];
