(* ::Package:: *)

IntegrateG[func_,{var_,ll_,ul_}]:=IntegralG[Expand[func/.flipArgument[1-var]],{var,ll,ul}]/;FreeQ[func,Alternatives@@DeleteCases[allIrreducibleFunctions,G]];
IntegrateG[func_,{var_,ll_,ul_}]:=(Print["Warning: expression contains irreducible functions. These will not be integrated."];IntegralG[Expand[func],{var,ll,ul}])/;!FreeQ[func,Alternatives@@DeleteCases[allIrreducibleFunctions,G]];

IntegralG[func_,{var_,0,0}]:=0;
IntegralG[func_,{var_,ll_,ul_}]:=IntegralG[func,{var,0,ul}]-IntegralG[func,{var,0,ll}]/;ll=!=0;
IntegralG[func_,{var_,0,ul_}]:=Module[{replaceVar=(Reduce[var==\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/.Equal[a_,b_]:>Rule[a,b]),integrand,improperArgs},
  integrand=Apart[toLinearBasisG[Expand[func]]/.replaceVar,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]];
  improperArgs=Select[DeleteCases[DeleteDuplicates[Flatten[Reap[integrand/.G[_,a_]:>Sow[a]][[2]]]],\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]],!FreeQ[#,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]&];
  If[Length[improperArgs]>0,Print["Multiple Polylogs of argument "<>ToString[improperArgs/.\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]->var,InputForm]<>" present. Symbolic cannot be carried out on these terms."]];
  Expand[toStrictLyndonBasis[Expand[integrand]/.
  {G[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]:>G[Prepend[aVec,0],temp],G[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/Plus[\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],a_]:>G[Prepend[aVec,-Plus[a]],temp],G[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/Plus[-\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],a_]:>-G[Prepend[aVec,Plus[a]],temp],Power[\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],-1]:>G[{0},temp],Power[Plus[\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],a_],-1]:>(G[{-a},temp]+G[{1},1+a]),Power[Plus[-\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],a_],-1]:>-(G[{a},temp]+G[{1},1-a])}/.temp->ul]]]/;ul=!=0\[And]FreeQ[ul,1];
IntegralG[func_,{var_,0,1}]:=Module[{replaceVar=(Reduce[var==\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/.Equal[a_,b_]:>Rule[a,b]),integrand,improperArgs},
  integrand=Apart[toLinearBasisG[Expand[func]]/.replaceVar,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]];
  improperArgs=Select[DeleteCases[DeleteDuplicates[Flatten[Reap[integrand/.G[_,a_]:>Sow[a]][[2]]]],\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]],!FreeQ[#,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]&];
  If[Length[improperArgs]>0,Print["Multiple Polylogs of argument "<>ToString[improperArgs/.\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]->var,InputForm]<>" present. Symbolic cannot be carried out on these terms."]];
  Expand[toStrictLyndonBasis[Expand[integrand]/.
  {G[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]:>G[Prepend[aVec,0],temp],G[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/Plus[\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],a_]:>G[Prepend[aVec,-Plus[a]],temp],G[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/Plus[-\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],a_]:>-G[Prepend[aVec,Plus[a]],temp],Power[\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],-1]:>G[{0},temp],Power[Plus[\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],a_],-1]:>(G[{-a},temp]+G[{1},1+a]),Power[Plus[-\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],a_],-1]:>-(G[{a},temp]+G[{1},1-a])}]/.flipArgument[temp]/.HPL[{___,1},1-temp]->0]];

IntegrateHPL[func_,{var_,ll_,ul_}]:=IntegralHPL[Expand[func/.flipArgument[1-var]],{var,ll,ul}]/;FreeQ[func,Alternatives@@allIrreducibleFunctions];
IntegrateHPL[func_,{var_,ll_,ul_}]:=(Print["Warning: expression contains irreducible and/or G functions. These will not be integrated."];IntegralHPL[Expand[func],{var,ll,ul}])/;!FreeQ[func,Alternatives@@allIrreducibleFunctions];

IntegralHPL[func_,{var_,0,0}]:=0;
IntegralHPL[func_,{var_,ll_,ul_}]:=IntegralHPL[func,{var,0,ul}]-IntegralHPL[func,{var,0,ll}]/;ll=!=0;
IntegralHPL[func_,{var_,0,ul_}]:=Module[{replaceVar=(Reduce[var==\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/.Equal[a_,b_]:>Rule[a,b]),integrand,improperArgs},
  integrand=Apart[toLinearBasis[func]/.replaceVar,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]];
  improperArgs=Select[DeleteCases[DeleteDuplicates[Flatten[Reap[integrand/.HPL[_,a_]:>Sow[a]][[2]]]],\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]],!FreeQ[#,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]&];
  If[Length[improperArgs]>0,Print["Harmonic Polylogs of argument "<>ToString[improperArgs/.\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]->var,InputForm]<>" present. Symbolic cannot be carried out on these terms."]];
  Expand[toStrictLyndonBasis[Expand[integrand]/.
  {HPL[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]:>HPL[Prepend[aVec,0],temp],HPL[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/(1-\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]):>HPL[Prepend[aVec,1],temp],HPL[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/(\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]-1):>-HPL[Prepend[aVec,1],temp],Power[\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],-1]:>HPL[{0},temp],Power[1-\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],-1]:>HPL[{1},temp],Power[\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]-1,-1]:>-HPL[{1},temp]}/.temp->ul]]]/;ul=!=0\[And]FreeQ[ul,1];
IntegralHPL[func_,{var_,0,1}]:=Module[{replaceVar=(Reduce[var==\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/.Equal[a_,b_]:>Rule[a,b]),integrand,improperArgs},
  integrand=Apart[toLinearBasis[func]/.replaceVar,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]];
  improperArgs=Select[DeleteCases[DeleteDuplicates[Flatten[Reap[integrand/.HPL[_,a_]:>Sow[a]][[2]]]],\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]],!FreeQ[#,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]&];
  If[Length[improperArgs]>0,Print["Harmonic Polylogs of argument "<>ToString[improperArgs/.\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]->var,InputForm]<>" present. Symbolic cannot be carried out on these terms."]];
  Expand[toStrictLyndonBasis[Expand[integrand]/.
  {HPL[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]:>HPL[Prepend[aVec,0],temp],HPL[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/(1-\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]):>HPL[Prepend[aVec,1],temp],HPL[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/(\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]-1):>-HPL[Prepend[aVec,1],temp],Power[\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],-1]:>HPL[{0},temp],Power[1-\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],-1]:>HPL[{1},temp],Power[\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]-1,-1]:>-HPL[{1},temp]}]/.flipArgument[temp]/.HPL[{___,1},1-temp]->0]];
IntegralHPL[func_,{var_,0,ul_->1}]:=Module[{replaceVar=(Reduce[var==\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/.Equal[a_,b_]:>Rule[a,b]),integrand,improperArgs},
  integrand=Apart[toLinearBasis[func]/.replaceVar,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]];
  improperArgs=Select[DeleteCases[DeleteDuplicates[Flatten[Reap[integrand/.HPL[_,a_]:>Sow[a]][[2]]]],\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]],!FreeQ[#,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]&];
  If[Length[improperArgs]>0,Print["Harmonic Polylogs of argument "<>ToString[improperArgs/.\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]->var,InputForm]<>" present. Symbolic cannot be carried out on these terms."]];
  Expand[toStrictLyndonBasis[Expand[integrand]/.
  {HPL[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]:>HPL[Prepend[aVec,0],temp],HPL[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/(1-\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]):>HPL[Prepend[aVec,1],temp],HPL[aVec_,\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]]/(\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]-1):>-HPL[Prepend[aVec,1],temp],Power[\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],-1]:>HPL[{0},temp],Power[1-\[CapitalOmega]\[CapitalOmega]\[CapitalOmega],-1]:>HPL[{1},temp],Power[\[CapitalOmega]\[CapitalOmega]\[CapitalOmega]-1,-1]:>-HPL[{1},temp]}]/.flipArgument[temp]/.{HPL[{___,1},1-temp]->0,HPL[{0},1-temp]->(-HPL[{1}, ul])}]];
