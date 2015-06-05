(* ::Package:: *)

LogsToHPL={Log[1-x_]:>HPL[{0},1-x],Log[x_]:>-HPL[{1},1-x],PolyLog[n_,x_]:>HPL[PadLeft[{1},n],x],PolyLog[i_,j_,y_]:>HPL[PadLeft[ConstantArray[1,j],i+j],y]};
LogsToG={func_:>Expand[func/.LogsToIMPL/.IMPLtoG]};
LogsToGI={Log[x_]:>(Log[x]/.LogsToHPL/.HPLtoGI)/;MatchQ[x,Alternatives[u,v,w,1-u,1-v,1-w]], PolyLog[n_,x_]:>(PolyLog[n,x]/.LogsToHPL/.HPLtoGI)/;MatchQ[x,Alternatives[u,v,w,1-u,1-v,1-w]], PolyLog[i_,j_,x_]:>(PolyLog[i,j,x]/.LogsToHPL/.HPLtoGI)/;MatchQ[x,Alternatives[u,v,w,1-u,1-v,1-w]], Log[x_]:>G[{0},x], Log[1-x_]:>G[{0},1-x], PolyLog[n_,x_]:>(-G[PadLeft[{1},n],x]),PolyLog[i_,j_,y_]:>Power[(-1),j]G[PadLeft[ConstantArray[1,j],i+j],y]};
LogsToGII={Log[x_]:>(Log[x]/.LogsToHPL/.HPLtoGII)/;MatchQ[x,Alternatives[u,v,w,1-u,1-v,1-w]], PolyLog[n_,x_]:>(PolyLog[n,x]/.LogsToHPL/.HPLtoGII)/;MatchQ[x,Alternatives[u,v,w,1-u,1-v,1-w]], PolyLog[i_,j_,x_]:>(PolyLog[i,j,x]/.LogsToHPL/.HPLtoGII)/;MatchQ[x,Alternatives[u,v,w,1-u,1-v,1-w]], Log[x_]:>G[{0},x], Log[1-x_]:>G[{0},1-x], PolyLog[n_,x_]:>(-G[PadLeft[{1},n],x]),PolyLog[i_,j_,y_]:>Power[(-1),j]G[PadLeft[ConstantArray[1,j],i+j],y]};
LogsToIMPL={Log[x_]:>IMPL[0,{0},x],PolyLog[n_,x_]:>-IMPL[0,PadRight[{1},n],x],PolyLog[i_,j_,y_]:>Power[(-1),j]IMPL[0,Reverse[PadLeft[ConstantArray[1,j],i+j]],y]};

HPLtoLogs=Join[Table[HPL[PadLeft[{},i],y_]->Log[y]^i/(i!),{i,10}],Table[HPL[PadLeft[{},i,1],1-y_]->(-Log[y])^i/(i!),{i,10}],Table[HPL[PadLeft[{1},i+1],y_]->PolyLog[i+1,y],{i,0,9}],Flatten[Table[Table[HPL[PadRight[PadRight[{},i],j,1],y_]->PolyLog[i,j-i,y],{j,i+2,10}],{i,2,8}]],{HPL[{0,1,1},y_]:>(Log[1-y]^2*Log[y])/2+Log[1-y]*PolyLog[2,1-y]-PolyLog[3,1-y]+\[Zeta][3],HPL[{0,1,1,1},y_]:>-((Log[1-y]^3*Log[y])/6+(Log[1-y]^2*PolyLog[2,1-y])/2-Log[1-y]*PolyLog[3,1-y]+PolyLog[4,1-y]-\[Zeta][4]),HPL[{0,1,1,1,1},y_]:>(Log[1-y]^4*Log[y])/24+(Log[1-y]^3*PolyLog[2,1-y])/6-(Log[1-y]^2*PolyLog[3,1-y])/2+Log[1-y]*PolyLog[4,1-y]-PolyLog[5,1-y]+\[Zeta][5],HPL[{0,1,1,1,1,1},y_]:>-((Log[1-y]^5*Log[y])/120+(Log[1-y]^4*PolyLog[2,1-y])/24-(Log[1-y]^3*PolyLog[3,1-y])/6+(Log[1-y]^2*PolyLog[4,1-y])/2-Log[1-y]*PolyLog[5,1-y]+PolyLog[6,1-y]-\[Zeta][6]),HPL[{0,1,1,1,1,1,1},y_]:>(Log[1-y]^6*Log[y])/720+(Log[1-y]^5*PolyLog[2,1-y])/120-(Log[1-y]^4*PolyLog[3,1-y])/24+(Log[1-y]^3*PolyLog[4,1-y])/6-(Log[1-y]^2*PolyLog[5,1-y])/2+Log[1-y]*PolyLog[6,1-y]-PolyLog[7,1-y]+\[Zeta][7],HPL[{0,1,1,1,1,1,1,1},y_]:>-((Log[1-y]^7*Log[y])/5040+(Log[1-y]^6*PolyLog[2,1-y])/720-(Log[1-y]^5*PolyLog[3,1-y])/120+(Log[1-y]^4*PolyLog[4,1-y])/24-(Log[1-y]^3*PolyLog[5,1-y])/6+(Log[1-y]^2*PolyLog[6,1-y])/2-Log[1-y]*PolyLog[7,1-y]+PolyLog[8,1-y]-\[Zeta][8]),HPL[{0,1,1,1,1,1,1,1,1},y_]:>(Log[1-y]^8*Log[y])/40320+(Log[1-y]^7*PolyLog[2,1-y])/5040-(Log[1-y]^6*PolyLog[3,1-y])/720+(Log[1-y]^5*PolyLog[4,1-y])/120-(Log[1-y]^4*PolyLog[5,1-y])/24+(Log[1-y]^3*PolyLog[6,1-y])/6-(Log[1-y]^2*PolyLog[7,1-y])/2+Log[1-y]*PolyLog[8,1-y]-PolyLog[9,1-y]+\[Zeta][9],HPL[{0,1,1,1,1,1,1,1,1,1},y_]:>-((Log[1-y]^9*Log[y])/362880+(Log[1-y]^8*PolyLog[2,1-y])/40320-(Log[1-y]^7*PolyLog[3,1-y])/5040+(Log[1-y]^6*PolyLog[4,1-y])/720-(Log[1-y]^5*PolyLog[5,1-y])/120+(Log[1-y]^4*PolyLog[6,1-y])/24-(Log[1-y]^3*PolyLog[7,1-y])/6+(Log[1-y]^2*PolyLog[8,1-y])/2-Log[1-y]*PolyLog[9,1-y]+PolyLog[10,1-y]-\[Zeta][10])}];
HPLtoG={func_:>Expand[func/.HPLtoIMPL/.IMPLtoG]};
HPLtoGI={func_:>Expand[takeHPLtoGI[toLinearBasis[func/.flipArgument[{1-u,1-v,1-w}]]]]/;FreeQ[func,Alternatives@@Join[{Log[__],IMPL[__]},allIrreducibleFunctions]]};
HPLtoGII={func_:>Expand[takeHPLtoGII[toLinearBasis[func/.flipArgument[{u,v,1-w}]]]]/;FreeQ[func,Alternatives@@Join[{Log[__],IMPL[__]},allIrreducibleFunctions]]};
HPLtoIMPL={HPL[aVec_,af_]:>IMPL[0,Reverse[decompressedNotation[aVec]],af](-1)^Count[aVec,1]};

GtoLogs=Join[Table[G[PadLeft[{},i],y_]->Log[y]^i/(i!),{i,10}],Table[G[PadLeft[{},i,1],1-y_]->Log[y]^i/(i!),{i,10}],Table[G[PadLeft[{1},i+1],y_]->-PolyLog[i+1,y],{i,1,9}],Flatten[Table[Table[G[PadRight[PadRight[{},i],j,1],y_]->(-1)^(j-i)PolyLog[i,j-i,y],{j,i+2,10}],{i,2,8}]],{G[{a_},var_]:>Log[1-var/a],G[{0,1,1},y_]:>(Log[1-y]^2*Log[y])/2+Log[1-y]*PolyLog[2,1-y]-PolyLog[3,1-y]+\[Zeta][3],G[{0,1,1,1},y_]:>(Log[1-y]^3*Log[y])/6+(Log[1-y]^2*PolyLog[2,1-y])/2-Log[1-y]*PolyLog[3,1-y]+PolyLog[4,1-y]-\[Zeta][4],G[{0,1,1,1,1},y_]:>(Log[1-y]^4*Log[y])/24+(Log[1-y]^3*PolyLog[2,1-y])/6-(Log[1-y]^2*PolyLog[3,1-y])/2+Log[1-y]*PolyLog[4,1-y]-PolyLog[5,1-y]+\[Zeta][5],G[{0,1,1,1,1,1},y_]:>(Log[1-y]^5*Log[y])/120+(Log[1-y]^4*PolyLog[2,1-y])/24-(Log[1-y]^3*PolyLog[3,1-y])/6+(Log[1-y]^2*PolyLog[4,1-y])/2-Log[1-y]*PolyLog[5,1-y]+PolyLog[6,1-y]-\[Zeta][6],G[{0,1,1,1,1,1,1},y_]:>(Log[1-y]^6*Log[y])/720+(Log[1-y]^5*PolyLog[2,1-y])/120-(Log[1-y]^4*PolyLog[3,1-y])/24+(Log[1-y]^3*PolyLog[4,1-y])/6-(Log[1-y]^2*PolyLog[5,1-y])/2+Log[1-y]*PolyLog[6,1-y]-PolyLog[7,1-y]+\[Zeta][7],G[{0,1,1,1,1,1,1,1},y_]:>(Log[1-y]^7*Log[y])/5040+(Log[1-y]^6*PolyLog[2,1-y])/720-(Log[1-y]^5*PolyLog[3,1-y])/120+(Log[1-y]^4*PolyLog[4,1-y])/24-(Log[1-y]^3*PolyLog[5,1-y])/6+(Log[1-y]^2*PolyLog[6,1-y])/2-Log[1-y]*PolyLog[7,1-y]+PolyLog[8,1-y]-\[Zeta][8],G[{0,1,1,1,1,1,1,1,1},y_]:>(Log[1-y]^8*Log[y])/40320+(Log[1-y]^7*PolyLog[2,1-y])/5040-(Log[1-y]^6*PolyLog[3,1-y])/720+(Log[1-y]^5*PolyLog[4,1-y])/120-(Log[1-y]^4*PolyLog[5,1-y])/24+(Log[1-y]^3*PolyLog[6,1-y])/6-(Log[1-y]^2*PolyLog[7,1-y])/2+Log[1-y]*PolyLog[8,1-y]-PolyLog[9,1-y]+\[Zeta][9],G[{0,1,1,1,1,1,1,1,1,1},y_]:>(Log[1-y]^9*Log[y])/362880+(Log[1-y]^8*PolyLog[2,1-y])/40320-(Log[1-y]^7*PolyLog[3,1-y])/5040+(Log[1-y]^6*PolyLog[4,1-y])/720-(Log[1-y]^5*PolyLog[5,1-y])/120+(Log[1-y]^4*PolyLog[6,1-y])/24-(Log[1-y]^3*PolyLog[7,1-y])/6+(Log[1-y]^2*PolyLog[8,1-y])/2-Log[1-y]*PolyLog[9,1-y]+PolyLog[10,1-y]-\[Zeta][10]}];
GtoHPL={G[aVec_,af_]:>HPL[aVec,af](-1)^Count[aVec,1]/;Count[aVec,Alternatives[0,-1,1]]==Length[aVec]};
GtoIMPL={G[aVec_,af_]:>IMPL[0,Reverse[aVec],af]};

MPLtoHPL={MPL[aVec_,af_]:>HPL[aVec,af](-1)^Count[aVec,1]};

IMPLtoLogs=Join[Table[IMPL[0,PadLeft[{},i],y_]->Log[y]^i/(i!),{i,10}],Table[IMPL[0,PadLeft[{},i,1],1-y_]->-(-Log[y])^i/(i!),{i,10}],Table[IMPL[0,PadRight[{1},i+1],y_]->-PolyLog[i+1,y],{i,0,9}]];
IMPLtoHPL={IMPL[0,aVec_,af_]:>(-1)^Count[aVec,1]HPL[Reverse[aVec],af]/;Count[aVec,Alternatives[0,-1,1]]==Length[aVec]};
IMPLtoG={IMPL[0,aVec_,af_]:>G[Reverse[aVec],af]};

toLogs=Join[HPLtoLogs,GtoLogs,IMPLtoLogs];
toHPL=Join[LogsToHPL,GtoHPL,IMPLtoHPL];
toGI=Join[LogsToGI,HPLtoGI,IMPLtoG,{func_:>irrToGI[func]/;MatchQ[func,Alternatives@@allIrreducibleFunctions]}];
toGII=Join[LogsToGII,HPLtoGII,IMPLtoG,{func_:>irrToGII[func]/;MatchQ[func,Alternatives@@allIrreducibleFunctions]}];
toIMPL=Join[LogsToIMPL,HPLtoIMPL,GtoIMPL];

toHPLorG[func_]:=Expand[func/.toHPL]/;FreeQ[func,Alternatives[yu,yv,yw]];
toHPLorG[func_]:=Expand[func/.IMPLtoG]/;FreeQ[func,Alternatives[u,v,w]];
toHPLorGI[func_]:=Expand[func/.toHPL]/;FreeQ[func,Alternatives[yu,yv,yw]];
toHPLorGI[func_]:=Expand[func/.toGI]/;FreeQ[func,Alternatives[u,v,w]];
toHPLorGII[func_]:=Expand[func/.toHPL]/;FreeQ[func,Alternatives[yu,yv,yw]];
toHPLorGII[func_]:=Expand[func/.toGII]/;FreeQ[func,Alternatives[u,v,w]];

takeHPLtoGI[func_]:=func/.HPL->convertHPLtoGI;
convertHPLtoGI[m_,x_]:=convertHPLtoGI[m,x]=(-1)^Count[m,1]Fold[IntGI,1,Reverse[m]/.{0->x,1->1-x}];
IntGI[a_,u]:=IntGI[a,yu]+IntGI[a,1-yv]-IntGI[a,1-yu*yv]+IntGI[a,1-yw]-IntGI[a,1-yu*yw]
IntGI[a_,v]:=IntGI[a,1-yu]+IntGI[a,yv]-IntGI[a,1-yu*yv]+IntGI[a,1-yw]-IntGI[a,1-yv*yw]
IntGI[a_,w]:=IntGI[a,1-yu]+IntGI[a,1-yv]+IntGI[a,yw]-IntGI[a,1-yu*yw]-IntGI[a,1-yv*yw]
IntGI[a_,1-u]:=IntGI[a,1-yu]-IntGI[a,1-yu*yv]-IntGI[a,1-yu*yw]+IntGI[a,1-yu*yv*yw]
IntGI[a_,1-v]:=IntGI[a,1-yv]-IntGI[a,1-yu*yv]-IntGI[a,1-yv*yw]+IntGI[a,1-yu*yv*yw]
IntGI[a_,1-w]:=IntGI[a,1-yw]-IntGI[a,1-yu*yw]-IntGI[a,1-yv*yw]+IntGI[a,1-yu*yv*yw]
IntGI[a_,yu]:=IntegrateGI[a/.G[_,yv]->0/.G[_,yw]->0,yu,0]
IntGI[a_,yv]:=IntegrateGI[a/.G[_,yw]->0,yv,0]
IntGI[a_,yw]:=IntegrateGI[a,yw,0]
IntGI[a_,1-yu]:=IntegrateGI[a/.G[_,yv]->0/.G[_,yw]->0,yu,1]
IntGI[a_,1-yv]:=IntegrateGI[a/.G[_,yw]->0,yv,1]
IntGI[a_,1-yw]:=IntegrateGI[a,yw,1]
IntGI[a_,1-yu*yv]:=IntegrateGI[a/.G[_,yw]->0,yv,1/yu]
IntGI[a_,1-yu*yw]:=IntegrateGI[a,yw,1/yu]
IntGI[a_,1-yv*yw]:=IntegrateGI[a,yw,1/yv]
IntGI[a_,1-yu*yv*yw]:=IntegrateGI[a,yw,1/yu/yv]
IntegrateGI[expr__,z_,c_]:=Expand[(G[{c},z]-1)(expr/. G[a__,z]:>0)+(expr/. G[{a___},z]:>G[{c,a},z])]

takeHPLtoGII[func_]:=func/.HPL->convertHPLtoGII;
convertHPLtoGII[m_,x_]:=convertHPLtoGII[m,x]=(-1)^Count[m,1]Fold[IntGII,1,Reverse[m]/.{0->x,1->1-x}];
IntGII[a_,u]:=IntGII[a,1-1/yv]+IntGII[a,1-yw]-IntGII[a,1-1/yu*1/yv]-IntGII[a,1-yu*yw]
IntGII[a_,v]:=IntGII[a,1-1/yu]+IntGII[a,1-yw]-IntGII[a,1-1/yu*1/yv]-IntGII[a,1-yv*yw]
IntGII[a_,w]:=IntGII[a,1-1/yu]+IntGII[a,1-1/yv]-IntGII[a,1/yu]-IntGII[a,1/yv]+IntGII[a,yw]-IntGII[a,1-yu*yw]-IntGII[a,1-yv*yw]
IntGII[a_,1-u]:=IntGII[a,1-1/yu]+IntGII[a,1-yu*yv*yw]-IntGII[a,1-1/yu*1/yv]-IntGII[a,1-yu*yw]+IntGII[a,1/yv]
IntGII[a_,1-v]:=IntGII[a,1-1/yv]+IntGII[a,1-yu*yv*yw]-IntGII[a,1-1/yu*1/yv]-IntGII[a,1-yv*yw]+IntGII[a,1/yu]
IntGII[a_,1-w]:=IntGII[a,1-yw]-IntGII[a,1-yu*yw]-IntGII[a,1-yv*yw]+IntGII[a,1-yu*yv*yw]
IntGII[a_,1/yu]:=IntegrateGII[a/.G[b__,1/yv]:>0/.G[b__,yw]:>0,1/yu,0]
IntGII[a_,1/yv]:=IntegrateGII[a/.G[b__,yw]:>0,1/yv,0]
IntGII[a_,yw]:=IntegrateGII[a,yw,0]
IntGII[a_,1-1/yu]:=IntegrateGII[a/.G[b__,1/yv]:>0/.G[b__,yw]:>0,1/yu,1]
IntGII[a_,1-1/yv]:=IntegrateGII[a/.G[b__,yw]:>0,1/yv,1]
IntGII[a_,1-yw]:=IntegrateGII[a,yw,1]
IntGII[a_,1-1/yu*1/yv]:=IntegrateGII[a/.G[b__,yw]:>0,1/yv,yu]
IntGII[a_,1-yu*yw]:=IntegrateGII[a,yw,1/yu]
IntGII[a_,1-yv*yw]:=IntegrateGII[a,yw,1/yv]
IntGII[a_,1-yu*yv*yw]:=IntegrateGII[a,yw,1/(yu*yv)]
IntegrateGII[expr__,z_,c_]:=Expand[(G[{c},z]-1)(expr/.G[a__,z]:>0)+(expr/.G[{a___},z]:>G[{c,a},z])]

takeHPLtoDSG[func_]:=func/.HPL->convertHPLtoDSG;
convertHPLtoDSG[m_,x_]:=convertHPLtoDSG[m,x]=(-1)^Count[m,1]Fold[IntDSG,1,Reverse[m]/.{0->x,1->1-x}];
IntDSG[a_,u]:=IntegrateDSG[a,1-u,1]
IntDSG[a_,w]:=IntegrateDSG[a,1-u,1]
IntDSG[a_,1-u]:=IntegrateDSG[a,1-u,0]
IntDSG[a_,1-w]:=IntegrateDSG[a,1-w,0]
IntDSG[a_,1-u-w]:=IntegrateDSG[a,1-w,u]

(*IntDSG[a_,u]:=IntegrateDSG[a/.G[_,1-w]->0,u,1]
IntDSG[a_,w]:=IntegrateDSG[a,1-w,1]
IntDSG[a_,1-u]:=IntegrateDSG[a/.G[_,1-w]->0,1-u,0]
IntDSG[a_,1-w]:=IntegrateDSG[a,1-w,0]
IntDSG[a_,1-u-w]:=IntegrateDSG[a,1-w,u]*)

(*IntDSG[a_,u]:=IntegrateDSG[a,1-u,1]
IntDSG[a_,w]:=IntegrateDSG[a,1-w,1]
IntDSG[a_,1-u]:=IntegrateDSG[a,1-u,0]
IntDSG[a_,1-w]:=IntegrateDSG[a,1-w,0]
IntDSG[a_,1-u-w]:=IntegrateDSG[a,1-w,u]*)

(*IntDSG[a_,u]:=IntegrateDSG[a,u,0]
IntDSG[a_,w]:=IntegrateDSG[a,w,0]
IntDSG[a_,1-u]:=IntegrateDSG[a,u,1]
IntDSG[a_,1-w]:=IntegrateDSG[a,w,1]
IntDSG[a_,1-u-w]:=IntegrateDSG[a,w,1-u]*)
IntegrateDSG[expr__,z_,c_]:=Expand[(G[{c},z]-1)(expr/. G[a__,z]:>0)+(expr/. G[{a___},z]:>G[{c,a},z])]

compressedNotation[vec_]:=Block[{ones=Position[vec,Alternatives[1,-1]][[All,1]], signs=DeleteCases[vec,0]},If[Last[vec]!=0,Join[signs[[1]]Take[ones,1],Table[(ones[[i+1]]-ones[[i]])signs[[i+1]],{i,1,Length@ones-1}]],Print["Cannot convert to compressed notation; last entry in HPL word is 0"]]]; (*Block[{ones=Position[vec,1][[All,1]]},If[Last[vec]==1,Join[Take[ones,1],Table[ones[[i+1]]-ones[[i]],{i,1,Length@ones-1}]],Print["Last entry in HPL word not a 1"]]];*)
decompressedNotation[vec_]:=Join@@Table[i/.{0:>{0},n_:>PadLeft[{Sign[n]},Abs[n]]/;n!=0},{i,vec}];
toCompressedNotation[func_]:=func/.HPL[aVec_,var_]:>HPL[compressedNotation[aVec],var];
toDecompressedNotation[func_]:=func/.(HPL[aVec_,var_]:>HPL[decompressedNotation[aVec],var]/;aVec!={0});

allIrreducibleFunctions={H3[_],H4[_],H5[_],H6[_],E7[_],O7[_],E8[_],O8[_],DS3[_],DS4[_],DS5[_],DS6[_],DS7[_],DS8[_],DS9[_],DS10[_],SP2[_],SP3[_],SP4[_],SP5[_],SP6[_],SP7[_],SP8[_],SP9[_],SP10[_], Subscript[OverTilde[\[CapitalPhi]],6], Superscript[\[CapitalOmega],"(2)"][_,_,_], Subscript[F,1][_,_,_], Subscript[H, 1][_,_,_], Subscript[J, 1][_,_,_], N, O, Subscript[M, 1][_,_,_], Subscript[Q, "ep"][_,_,_], G, Subscript[K, 1][_,_,_]};
(*oddIrreducibleFunctions={H3[1],H4[4],H4[5],H4[6],H5[1],H5[2],H5[3],H5[4],H5[5],H5[6],H5[20],H5[21],H5[22],H5[23],O7[_],Subscript[OverTilde[\[CapitalPhi]],6], Subscript[F,1][_,_,_], Subscript[H, 1][_,_,_], Subscript[J, 1][_,_,_], G, Subscript[K, 1][_,_,_]};
evenIrreducibleFunctions={H4[1],H4[2],H4[3],H5[7],H5[8],H5[9],H5[10],H5[11],H5[12],H5[13],H5[14], H5[15], H5[16],H5[17],H5[18],H5[19],E7[_],Superscript[\[CapitalOmega],"(2)"][_,_,_], N, O, Subscript[M, 1][_,_,_], Subscript[Q, "ep"][_,_,_]};*)
