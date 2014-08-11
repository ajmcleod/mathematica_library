(* ::Package:: *)

ClearAll[coproductD,replace\[CapitalDelta]];

coproductD[func_,u]:=coproductEntry[func,u]/u-coproductEntry[func,1-u]/(1-u)+coproductEntry[func,yu](1-u-v-w)/(u  Sqrt[\[CapitalDelta]])+coproductEntry[func,yv](1-u-v+w)/((1-u)Sqrt[\[CapitalDelta]])+coproductEntry[func,yw](1-u+v-w)/((1-u)Sqrt[\[CapitalDelta]]);
coproductD[func_,v]:=coproductEntry[func,v]/v-coproductEntry[func,1-v]/(1-v)+coproductEntry[func,yv](1-u-v-w)/(v Sqrt[\[CapitalDelta]])+coproductEntry[func,yw](1+u-v-w)/((1-v)Sqrt[\[CapitalDelta]])+coproductEntry[func,yu](1-u-v+w)/((1-v)Sqrt[\[CapitalDelta]]);
coproductD[func_,w]:=coproductEntry[func,w]/w-coproductEntry[func,1-w]/(1-w)+coproductEntry[func,yw](1-u-v-w)/(w Sqrt[\[CapitalDelta]])+coproductEntry[func,yu](1-u+v-w)/((1-w)Sqrt[\[CapitalDelta]])+coproductEntry[func,yv](1+u-v-w)/((1-w)Sqrt[\[CapitalDelta]]);
coproductD[func_,yu]:=coproductEntry[func,u](1-u)(1-v-w)/(yu Sqrt[\[CapitalDelta]])-coproductEntry[func,v]u (1-v)/(yu Sqrt[\[CapitalDelta]])-coproductEntry[func,w]u (1-w)/(yu Sqrt[\[CapitalDelta]])-coproductEntry[func,1-u]u (1-v-w)/(yu Sqrt[\[CapitalDelta]])+coproductEntry[func,1-v] u v/(yu Sqrt[\[CapitalDelta]])+coproductEntry[func,1-w] u w/(yu Sqrt[\[CapitalDelta]])+coproductEntry[func,yu]/(yu);
coproductD[func_,yv]:=coproductEntry[func,v](1-v)(1-u-w)/(yv Sqrt[\[CapitalDelta]])-coproductEntry[func,w]v (1-w)/(yv Sqrt[\[CapitalDelta]])-coproductEntry[func,u]v (1-u)/(yv Sqrt[\[CapitalDelta]])-coproductEntry[func,1-v]v (1-w-u)/(yv Sqrt[\[CapitalDelta]])+coproductEntry[func,1-w] v w/(yv Sqrt[\[CapitalDelta]])+coproductEntry[func,1-u] v u/(yv Sqrt[\[CapitalDelta]])+coproductEntry[func,yv]/(yv);
coproductD[func_,yw]:=coproductEntry[func,w](1-w)(1-v-u)/(yw Sqrt[\[CapitalDelta]])-coproductEntry[func,u]w (1-u)/(yw Sqrt[\[CapitalDelta]])-coproductEntry[func,v]w (1-v)/(yw Sqrt[\[CapitalDelta]])-coproductEntry[func,1-w]w (1-u-v)/(yw Sqrt[\[CapitalDelta]])+coproductEntry[func,1-u] w u/(yw Sqrt[\[CapitalDelta]])+coproductEntry[func,1-v] w v/(yw Sqrt[\[CapitalDelta]])+coproductEntry[func,yw]/(yw);
coproductD[func_,yu/yw]:=coproductEntry[func,u](1-u)(1-v)/Sqrt[\[CapitalDelta]]-coproductEntry[func,v](u-w)(1-v)/Sqrt[\[CapitalDelta]]-coproductEntry[func,w](1-v)(1-w)/Sqrt[\[CapitalDelta]]-coproductEntry[func,1-u]u (1-v)/Sqrt[\[CapitalDelta]]+coproductEntry[func,1-v]v (u-w)/Sqrt[\[CapitalDelta]]+coproductEntry[func,1-w]w (1-v)/Sqrt[\[CapitalDelta]]+coproductEntry[func,yu]-coproductEntry[func,yw];
coproductD[func_,yv/yu]:=coproductEntry[func,v](1-v)(1-w)/Sqrt[\[CapitalDelta]]-coproductEntry[func,w](v-u)(1-w)/Sqrt[\[CapitalDelta]]-coproductEntry[func,u](1-w)(1-u)/Sqrt[\[CapitalDelta]]-coproductEntry[func,1-v]v (1-w)/Sqrt[\[CapitalDelta]]+coproductEntry[func,1-w]w (v-u)/Sqrt[\[CapitalDelta]]+coproductEntry[func,1-u]u (1-w)/Sqrt[\[CapitalDelta]]+coproductEntry[func,yv]-coproductEntry[func,yu];
coproductD[func_,yw/yv]:=coproductEntry[func,w](1-w)(1-u)/Sqrt[\[CapitalDelta]]-coproductEntry[func,u](w-v)(1-u)/Sqrt[\[CapitalDelta]]-coproductEntry[func,v](1-u)(1-v)/Sqrt[\[CapitalDelta]]-coproductEntry[func,1-w]w (1-u)/Sqrt[\[CapitalDelta]]+coproductEntry[func,1-u]u (w-v)/Sqrt[\[CapitalDelta]]+coproductEntry[func,1-v]v (1-u)/Sqrt[\[CapitalDelta]]+coproductEntry[func,yw]-coproductEntry[func,yv];
coproductD[func_,yw/yu]:=coproductEntry[func,w](1-w)(1-v)/Sqrt[\[CapitalDelta]]-coproductEntry[func,v](w-u)(1-v)/Sqrt[\[CapitalDelta]]-coproductEntry[func,u](1-v)(1-u)/Sqrt[\[CapitalDelta]]-coproductEntry[func,1-w]w (1-v)/Sqrt[\[CapitalDelta]]+coproductEntry[func,1-v]v (w-u)/Sqrt[\[CapitalDelta]]+coproductEntry[func,1-u]u (1-v)/Sqrt[\[CapitalDelta]]+coproductEntry[func,yw]-coproductEntry[func,yu];
coproductD[func_,yu/yv]:=coproductEntry[func,u](1-u)(1-w)/Sqrt[\[CapitalDelta]]-coproductEntry[func,w](u-v)(1-w)/Sqrt[\[CapitalDelta]]-coproductEntry[func,v](1-w)(1-v)/Sqrt[\[CapitalDelta]]-coproductEntry[func,1-u]u (1-w)/Sqrt[\[CapitalDelta]]+coproductEntry[func,1-w]w (u-v)/Sqrt[\[CapitalDelta]]+coproductEntry[func,1-v]v (1-w)/Sqrt[\[CapitalDelta]]+coproductEntry[func,yu]-coproductEntry[func,yv];
coproductD[func_,yv/yw]:=coproductEntry[func,v](1-v)(1-u)/Sqrt[\[CapitalDelta]]-coproductEntry[func,u](v-w)(1-u)/Sqrt[\[CapitalDelta]]-coproductEntry[func,w](1-u)(1-w)/Sqrt[\[CapitalDelta]]-coproductEntry[func,1-v]v (1-u)/Sqrt[\[CapitalDelta]]+coproductEntry[func,1-u]u (v-w)/Sqrt[\[CapitalDelta]]+coproductEntry[func,1-w]w (1-u)/Sqrt[\[CapitalDelta]]+coproductEntry[func,yv]-coproductEntry[func,yw];
coproductD[func_,u,var_]:=coproductD[coproductEntry[func,u],var]/u-coproductD[coproductEntry[func,1-u],var]/(1-u)+coproductD[coproductEntry[func,yu],var](1-u-v-w)/(u  Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,yv],var](1-u-v+w)/((1-u)Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,yw],var](1-u+v-w)/((1-u)Sqrt[\[CapitalDelta]]);
coproductD[func_,v,var_]:=coproductD[coproductEntry[func,v],var]/v-coproductD[coproductEntry[func,1-v],var]/(1-v)+coproductD[coproductEntry[func,yv],var](1-u-v-w)/(v Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,yw],var](1+u-v-w)/((1-v)Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,yu],var](1-u-v+w)/((1-v)Sqrt[\[CapitalDelta]]);
coproductD[func_,w,var_]:=coproductD[coproductEntry[func,w],var]/w-coproductD[coproductEntry[func,1-w],var]/(1-w)+coproductD[coproductEntry[func,yw],var](1-u-v-w)/(w Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,yu],var](1+v-w-u)/((1-w)Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,yv],var](1-v-w+u)/((1-w)Sqrt[\[CapitalDelta]]);
coproductD[func_,yu,var_]:=coproductD[coproductEntry[func,u],var](1-u)(1-v-w)/(yu Sqrt[\[CapitalDelta]])-coproductD[coproductEntry[func,v],var]u (1-v)/(yu Sqrt[\[CapitalDelta]])-coproductD[coproductEntry[func,w],var]u (1-w)/(yu Sqrt[\[CapitalDelta]])-coproductD[coproductEntry[func,1-u],var]u (1-v-w)/(yu Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,1-v],var] u v/(yu Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,1-w],var] u w/(yu Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,yu],var]/(yu);
coproductD[func_,yv,var_]:=coproductD[coproductEntry[func,v],var](1-v)(1-u-w)/(yv Sqrt[\[CapitalDelta]])-coproductD[coproductEntry[func,w],var]v (1-w)/(yv Sqrt[\[CapitalDelta]])-coproductD[coproductEntry[func,u],var]v (1-u)/(yv Sqrt[\[CapitalDelta]])-coproductD[coproductEntry[func,1-v],var]v (1-w-u)/(yv Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,1-w],var] v w/(yv Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,1-u],var] v u/(yv Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,yv],var]/(yv);
coproductD[func_,yw,var_]:=coproductD[coproductEntry[func,w],var](1-w)(1-v-u)/(yw Sqrt[\[CapitalDelta]])-coproductD[coproductEntry[func,u],var]w (1-u)/(yw Sqrt[\[CapitalDelta]])-coproductD[coproductEntry[func,v],var]w (1-v)/(yw Sqrt[\[CapitalDelta]])-coproductD[coproductEntry[func,1-w],var]w (1-u-v)/(yw Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,1-u],var] w u/(yw Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,1-v],var] w v/(yw Sqrt[\[CapitalDelta]])+coproductD[coproductEntry[func,yw],var]/(yw);
coproductD[func_,Subscript[z,u]]:=Block[{fullFunction=func/.SVHPLreplacements},(1/Subscript[z,u])(coproductEntry[fullFunction,w]-coproductEntry[fullFunction,yw]+coproductEntry[fullFunction,Subscript[z,u]])+(1/(1-Subscript[z,u]))(coproductEntry[fullFunction,v]+coproductEntry[fullFunction,w]+coproductEntry[fullFunction,yv]-coproductEntry[fullFunction,yw]-coproductEntry[fullFunction,1-Subscript[z,u]])];
coproductD[func_,Subscript[z,v]]:=Block[{fullFunction=func/.SVHPLreplacements},(1/Subscript[z,v])(coproductEntry[fullFunction,u]-coproductEntry[fullFunction,yu]+coproductEntry[fullFunction,Subscript[z,v]])+(1/(1-Subscript[z,v]))(coproductEntry[fullFunction,w]+coproductEntry[fullFunction,u]+coproductEntry[fullFunction,yw]-coproductEntry[fullFunction,yu]-coproductEntry[fullFunction,1-Subscript[z,v]])];
coproductD[func_,Subscript[z,w]]:=Block[{fullFunction=func/.SVHPLreplacements},(1/Subscript[z,w])(coproductEntry[fullFunction,v]-coproductEntry[fullFunction,yv]+coproductEntry[fullFunction,Subscript[z,w]])+(1/(1-Subscript[z,w]))(coproductEntry[fullFunction,u]+coproductEntry[fullFunction,v]+coproductEntry[fullFunction,yu]-coproductEntry[fullFunction,yv]-coproductEntry[fullFunction,1-Subscript[z,w]])];
coproductD[func_,Subscript[zb,u]]:=Block[{fullFunction=func/.SVHPLreplacements},(1/Subscript[zb,u])(coproductEntry[fullFunction,w]+coproductEntry[fullFunction,yw]+coproductEntry[fullFunction,Subscript[zb,u]])+(1/(1-Subscript[zb,u]))(coproductEntry[fullFunction,v]+coproductEntry[fullFunction,w]-coproductEntry[fullFunction,yv]+coproductEntry[fullFunction,yw]-coproductEntry[fullFunction,1-Subscript[zb,u]])];
coproductD[func_,Subscript[zb,v]]:=Block[{fullFunction=func/.SVHPLreplacements},(1/Subscript[zb,v])(coproductEntry[fullFunction,u]+coproductEntry[fullFunction,yu]+coproductEntry[fullFunction,Subscript[zb,v]])+(1/(1-Subscript[zb,v]))(coproductEntry[fullFunction,w]+coproductEntry[fullFunction,u]-coproductEntry[fullFunction,yw]+coproductEntry[fullFunction,yu]-coproductEntry[fullFunction,1-Subscript[zb,v]])];
coproductD[func_,Subscript[zb,w]]:=Block[{fullFunction=func/.SVHPLreplacements},(1/Subscript[zb,w])(coproductEntry[fullFunction,v]+coproductEntry[fullFunction,yv]+coproductEntry[fullFunction,Subscript[zb,w]])+(1/(1-Subscript[zb,w]))(coproductEntry[fullFunction,u]+coproductEntry[fullFunction,v]-coproductEntry[fullFunction,yu]+coproductEntry[fullFunction,yv]-coproductEntry[fullFunction,1-Subscript[zb,w]])];
coproductD[func_,Subscript[\[Xi],u]]:=Block[{fullFunction=func/.SVHPLreplacements},(1/Subscript[\[Xi],u])(coproductEntry[fullFunction,1-u]+coproductEntry[fullFunction,v]+coproductEntry[fullFunction,w])];
coproductD[func_,Subscript[\[Xi],v]]:=Block[{fullFunction=func/.SVHPLreplacements},(1/Subscript[\[Xi],v])(coproductEntry[fullFunction,1-v]+coproductEntry[fullFunction,w]+coproductEntry[fullFunction,u])];
coproductD[func_,Subscript[\[Xi],w]]:=Block[{fullFunction=func/.SVHPLreplacements},(1/Subscript[\[Xi],w])(coproductEntry[fullFunction,1-w]+coproductEntry[fullFunction,u]+coproductEntry[fullFunction,v])];
coproductD[func_,z]:=coproductD[func,Subscript[z,u]];
coproductD[func_,zb]:=coproductD[func,Subscript[zb,u]];
coproductD[func_,\[Xi]]:=coproductD[func,Subscript[\[Xi],u]];

replace\[CapitalDelta]={\[CapitalDelta]->(1-u-v-w)^2-4u v w};

(*coproductD[func_,z]:=Block[{fullFunction=func/.SVHPLreplacements},(1/z)(coproductEntry[fullFunction,w]-coproductEntry[fullFunction,yw]+coproductEntry[fullFunction,z])+(1/(1-z))(coproductEntry[fullFunction,v]+coproductEntry[fullFunction,w]+coproductEntry[fullFunction,yv]-coproductEntry[fullFunction,yw]-coproductEntry[fullFunction,1-z])];
coproductD[func_,zb]:=Block[{fullFunction=func/.SVHPLreplacements},(1/zb)(coproductEntry[fullFunction,w]+coproductEntry[fullFunction,yw]+coproductEntry[fullFunction,zb])+(1/(1-zb))(coproductEntry[fullFunction,v]+coproductEntry[fullFunction,w]-coproductEntry[fullFunction,yv]+coproductEntry[fullFunction,yw]-coproductEntry[fullFunction,1-zb])];
coproductD[func_,\[Xi]]:=Block[{fullFunction=func/.SVHPLreplacements},(1/\[Xi])(coproductEntry[fullFunction,1-u]+coproductEntry[fullFunction,v]+coproductEntry[fullFunction,w])];
coproductD[func_,{u,u,1}]:=ReplaceAll[coproductEntry[func,u]+coproductEntry[func,v],{v->u,w->1}]/u-ReplaceAll[coproductEntry[func,1-u]+coproductEntry[func,1-v],{v->u,w->1}]/(1-u);
coproductD[func_,{1,v,v}]:=ReplaceAll[coproductEntry[func,v]+coproductEntry[func,w],{w->v,u->1}]/v-ReplaceAll[coproductEntry[func,1-v]+coproductEntry[func,1-w],{w->v,u->1}]/(1-v);
coproductD[func_,{w,1,w}]:=ReplaceAll[coproductEntry[func,w]+coproductEntry[func,u],{u->w,v->1}]/w-ReplaceAll[coproductEntry[func,1-w]+coproductEntry[func,1-u],{u->w,v->1}]/(1-w);*)

