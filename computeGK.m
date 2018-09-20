(* ::Package:: *)

(* 
implements the algorithm of Cho-Ikeda-Katsurada-Yamauchi 
to compute the extended Gross-keating invariant and the Siegel series of a half-integral matrix 
*)


BeginPackage["mmacomputeGK`"]


Block[{version, date},
 version="1.0";
 date = "(2018-09-20)";
 Print["computeGK Version "<> version];
 Print[" by Chul-hee Lee "<>date]
 ]


(* data types *)
blockdiag::usage="blockdiag is the head used for block diagonal matrices"
JC::usage="JC is the head used for Jordan components"
FJC::usage="JC is the head used for flat Jordan components"
H::usage="H is the symbol for the matrix {{0,1},{1,0}}/2"
Y::usage="Y is the symbol for the matrix {{2,1},{1,2}}/2"
(* commands *)
getFJCfromJC::usage ="getFJCfromJC[expr] converts a JC into a FJC"
(* getWJCfromFJC::usage="collects the diagoanl components with the same exponent" *)
getJCfromFJC::usage ="getJCfromFJC[expr] converts a FJC into a JC"
getBdiag::usage="getBdiag[expr] yields a blockdiag expression"
getMatrix::usage="getMatrix[expr] yields a matrix corresponding to expr"
rndBdiag::usage=""
rndFJC::usage=""
rndOddFJC::usage=""
rndMat::usage=""
rndOddMat::usage=""
rndposdef::usage=""
rndDiagMat::usage=""
rndposdef::usage=""
(* main instructions *)
jcprop::usage=""
checkWeakCanonicalFormQ::usage="checkWeakCanonicalFormQ[expr] gives True if expr is a weak canonical form, and False otherwise."
checkPreOptimalFormQ::usage="checkPreOptimalFormQ[expr] gives True if expr is a pre-optimal form, and False otherwise."
checkNEGKdatumQ::usage="checkNEGKdatumQ[expr] gives True if expr is a naive EGK datum, and False otherwise."
checkFpolyDual::usage="checkFpolyDual[expr,p] gives True if computeFpoly[expr,p,X] satisfies a certain functional equation, and False otherwise"
checkGKtripleQ::usage="checkGKtripleQ[m1,m2,m3] gives {True, Qlist} if the arithmetic intersection number for (m1,m2m3) is finite together with a list and False otherwise"
reduceJordanZp::usage=""
reduceJordanK::usage=""
reduceWatson::usage=""
reduceWeakCanonical::usage=""
reducePreOptimal::usage=""
computeGK::usage="computeGK[expr,prime] yields the GK invariant of a JC expr"
computeGK2::usage="computeGK2[expr] yields the GK invariant of a JC expr"
computeNEGKdatum::usage="computeNEGKdatum[expr,prime] yields a naive EGK datum of a JC expr"
computeFpoly::usage="computeFpoly[expr,prime,var] yields the Siegel series of a JC expr in variable var"
computeGKint::usage="computeGKint[expr] yields the factors of the arithmetic intersection number for expr"
(*temp/test*)
(*
HilbertSymbol::usage=""
HasseInvariant::usage=""
GrossKeatingInv::usage=""
GrossKeatingAlpha::usage=""
GrossKeatingBeta::usage=""
GKcontrib::usage=""
Valuation::usage=""
QpTernaryAnisotropicPrimes::usage=""
QpTernaryIsotropicQ::usage=""
Lptsbdy::usage=""
L1list::usage=""
L2list::usage=""
WatsonSplit::usage=""
FpLaurent::usage=""
computeGKbyCY::usage=""
chip::usage=""
xip::usage=""
etap::usage=""
jcpropseq::usage=""
MyMinEntry::usage=""
ElementaryMatrix1::usage=""
ElementaryMatrix3::usage=""
BlockMatrix::usage=""
*)


Begin["`Priviate`"];


(* quadratic form basics *)
Valuation[x_,p_]:=IntegerExponent[Numerator[x],p]-IntegerExponent[Denominator[x],p];
HilbertSymbol[a_,b_,\[Infinity]]:=Which[
a>0||b>0,1,
a<0&&b<0,-1,
True,1
]
HilbertSymbol[aa_,bb_,p_]:=Block[{a,b,\[Alpha],\[Beta],u,v,\[Epsilon],\[Omega]},
a=Numerator[aa]*Denominator[aa];b=Numerator[bb]*Denominator[bb];
\[Alpha]=IntegerExponent[a,p];
\[Beta]=IntegerExponent[b,p];
u=a/p^\[Alpha];
v=b/p^\[Beta];
\[Epsilon][x_]:=(x-1)/2;
\[Omega][x_]:=(x^2-1)/8;
If[p==2,
(-1)^( \[Epsilon][u]\[Epsilon][v]+\[Alpha] \[Omega][v]+\[Beta] \[Omega][u]),
(-1)^(\[Alpha] \[Beta] \[Epsilon][p]) JacobiSymbol[u,p]^\[Beta] JacobiSymbol[v,p]^\[Alpha]]
]
(* i<j; without equality *)
HasseInvariant[diag_List,p_Integer]:=Block[{a,len},
len=Length[diag];
Product[HilbertSymbol[diag[[i]],diag[[j]],p],{i,1,len},{j,i+1,len}]
]
(* i\[LessEqual]j; with equality *)
HasseInvariant2[diag_List,p_Integer]:=Block[{a,len},
len=Length[diag];
Product[HilbertSymbol[diag[[i]],diag[[j]],p],{i,1,len},{j,i,len}]
]
(* main reference : Katsurada 428p, King section 7 *)
chip[a_,p_]:=Block[{r,c,val},
(* a= p^r*c *)
r=Valuation[a,p];
c=a/p^r;c=Numerator[c]*Denominator[c];
val=Which[
OddQ[p]&&EvenQ[r], JacobiSymbol[c,p],
p==2&&EvenQ[r]&&Mod[c,8]==1,1,
p==2&&EvenQ[r]&&Mod[c,8]==5,-1,
True,0
];
val
]
xip[diag_List,p_]:=Block[{m,det},
m=Length[diag];det=Times@@diag;
chip[(-1)^(m/2)*det,p]
]/;EvenQ[Length[diag]]
degree[B_blockdiag]:=Total@(Length/@List@@B)
determinant[B_blockdiag]:=Times@@(Det/@B)
etap[diag_List,p_]:=Block[{m,det},
m=Length[diag];det=Times@@diag;
HasseInvariant2[diag,p]*HilbertSymbol[det,(-1)^((m-1)/2) det,p]*(HilbertSymbol[-1,-1,p])^((m^2-1)/8)
]/;OddQ[Length[diag]]


(* some basic operations on data type *)
(* conversion between FJC and JC *)
getFJCfromJC[JC[]]=FJC[];
getFJCfromJC[jcomp_JC]:=FJC@@Flatten[Map[Distribute[#,List]&,List@@jcomp],1]
getJCfromFJC[FJC[]]=JC[];
getJCfromFJC[fjc_FJC]:=JC@@({#[[1]],{#[[2]]}}&/@fjc)
getBdiag[jc_JC]:=getBdiag[getFJCfromJC@jc]
getBdiag[jc_FJC]:=Block[{B,rule,temp},
rule={H->1/2 {{0,1},{1,0}},Y->1/2 {{2,1},{1,2}}};
temp[x_]:=If[NumberQ[x],{{x}},x/. rule];
B=(2^(#1[[1]])*temp[#1[[2]]]&)/@jc;
blockdiag@@B
]
(* input: short fjc *)
getWJCfromFJC[FJC[]]=JC[];
getWJCfromFJC[fjc_FJC]:=Block[{temp,lasttemp,kr,type,Jr={}},
temp=List@@fjc;
lasttemp = Last[temp];
PrependTo[Jr,lasttemp];
kr=lasttemp[[1]];type=NumberQ[lasttemp[[2]]];
temp=Drop[temp,-1];
While[temp!={}&&kr==Last[temp][[1]]&&NumberQ[Last[temp][[2]]],
PrependTo[Jr,Last[temp]];
temp=Drop[temp,-1];
];
Append[getWJCfromFJC[FJC@@temp],{Jr[[1]][[1]],Map[#[[2]]&,Jr]}]
]
getMatrix[B_blockdiag]:=Normal[SparseArray[Band[{1,1}]->{##}]&@@B]
getMatrix[fjc_FJC]:=getMatrix[getBdiag@fjc]
getMatrix[jc_JC]:=getMatrix[getBdiag@jc]


rndFJC[size_]:=Block[{degset,rr,numlist,matlist,rnd,sum,rule},
sum=0;degset={};
While[sum<=size-3,
rnd = RandomChoice[{1,1,2}];
sum+=rnd;
AppendTo[degset,rnd];
];
If[size-sum==1,AppendTo[degset,1],AppendTo[degset,2]];
rr=Length[degset];
numlist = RandomChoice[Range[0,2*rr],rr];
matlist ={};
Do[
If[deg==1,AppendTo[matlist,RandomChoice[{1,3,5,7}]],
AppendTo[matlist,RandomChoice[{H,Y}]]],
{deg,degset}
];
FJC@@(Transpose[{numlist,matlist}])
]
rndBdiag[size_]:=getBdiag@rndFJC[size]
rndMat[size_]:=getMatrix[rndBdiag[size]]
rndOddFJC[size_:20]:=Block[{nogo,explist,count,ulist},
nogo=True;explist={};count=0;
While[nogo,
explist = Join[explist,ConstantArray[count,RandomChoice[{0,1,2}]]];
nogo=Length[explist]<size;
count++
];
explist =explist[[;;size]];
ulist=RandomChoice[{1,3,5,7},size];
FJC@@Transpose[{explist, ulist}]
]
rndOddMat[size_:20]:=getMatrix[rndOddFJC[size]]
(* generate a random positive definite matrix of given size *)
rndDiagMat[size_,range_]:=DiagonalMatrix@RandomInteger[{1,range},size]
rndposdef[1,range_,opt_:"even"]:={{#}}&@If[opt=="even",2RandomInteger[{1,range}],RandomInteger[{1,range}]];
rndposdef[size_,range_,opt_:"even"]:=
Block[{A,found,a,counter},
found=False;counter=0;
While[Not[found],
If[counter==0,A[0] = rndposdef[size-1,range,opt];Do[a[i,j]=A[0][[i,j]],{i,1,size-1},{j,1,size-1}]];
Do[a[size,i]=a[i,size]=RandomInteger[{-range,range}],{i,1,size-1}];
a[size,size]=If[opt=="even",2RandomInteger[{1,range}],RandomInteger[{1,range}]];
A[1]=Array[a,{size,size}];
found=Det[A[1]]>0;
counter=Mod[counter+1,100];
];
A[1]
]


Clear[jcprop,jcpropseq]
(* jcprop assume that the input is short *)
jcprop[JC[],2]={"shortQ"->True,"degB"->0,"udet"->1,"ordetB2"->0,"ordetB"->0,"eps"->1};
jcprop[jc_JC,2]:=jcprop[jc,2]=Block[{p=2,krCr,kr,Cr,B1,shortQ,degB,udet,orderB2,ordetB2,ordetB,eps,degC},
(* diagonalize 2H&2Y over Q2 using ;
{{1,1},{-(1/2),1/2}}.{{0,1},{1,0}}.Transpose[{{1,1},{-(1/2),1/2}}] =={{2,0},{0,-(1/2)}};
Transpose[{{1,-(1/2)},{1,1/2}}].{{2,1},{1,2}}.{{1,-(1/2)},{1,1/2}} =={{6,0},{0,1/2}};
*)
krCr = Last[jc];
{kr,Cr}={Mod[#[[1]],2],#[[2]]/.{H->Sequence[1,-1],Y->Sequence[3,1]}}&@krCr;
degC=Length[Cr];
B1=Drop[jc,-1];
{shortQ,degB,udet,ordetB2,ordetB,eps}={"shortQ","degB","udet","ordetB2","ordetB","eps"}/.jcprop[B1,p];
If[shortQ&&(1<=degC<=2),
degB=degB+degC;
eps =eps*(If[degC==1,HilbertSymbol[udet*p^ordetB2,p^kr Cr[[1]],p],HilbertSymbol[udet*p^ordetB2,Cr[[1]]*Cr[[2]],p]*HilbertSymbol[p^kr*Cr[[1]],p^kr*Cr[[2]],p]]);
udet=Mod[udet*(Times@@Cr),8];
ordetB2=Mod[ordetB2+degC*kr,2];
ordetB = ordetB+(degC*krCr[[1]]-If[MemberQ[{{H},{Y}},krCr[[2]]],2,0]);
{"shortQ"->True,"degC"->degC,"degB"->degB,"udet"->udet,"ordetB2"->ordetB2,"ordetB"->ordetB,"eps"->eps},
{"shortQ"->False}]
]
jcprop[jc_JC,p_,opt_String]:=Block[{prevaltypes,degB,udet,ordetB2,ordetB,eps,xiB,deltaB,temp},
prevaltypes=First/@jcprop[jc,p];
Which[
MemberQ[prevaltypes,opt],opt/.jcprop[jc,p],
opt=="kr",First@Last@jc,
opt=="xi",
{degB,udet,ordetB2}={"degB","udet","ordetB2"}/.jcprop[jc,p];temp = chip[(-1)^Floor[degB/2]*udet*p^ordetB2,p];AppendTo[jcprop[jc,p],"xi"->temp];
jcprop[jc,p,opt],
opt=="eta",
{degB,udet,ordetB2,eps}={"degB","udet","ordetB2","eps"}/.jcprop[jc,p];
temp = (HilbertSymbol[-1,-1,p])^(Floor[(degB+1)/4])*HilbertSymbol[-1,udet*p^ordetB2,p]^Floor[(degB-1)/2]*eps;
AppendTo[jcprop[jc,p],"eta"->temp];
jcprop[jc,p,opt],
p==2&&opt=="Delta",
(* Cho-Ikeda-Katsurada-Yamauchi,arXiv1709.02772v1;remarks on EGK; page 17 *)
{degB,ordetB2,ordetB}={"degB","ordetB2","ordetB"}/.jcprop[jc,p];
xiB = jcprop[jc,p,"xi"];
eps = Which[
EvenQ[degB]&&OddQ[ordetB2],degB-2,
EvenQ[degB]&&EvenQ[ordetB2]&&xiB==0,degB-1,
EvenQ[degB]&&EvenQ[ordetB2]&&xiB!=0,degB,
OddQ[degB],(degB-1)
];
temp = ordetB+(eps);
AppendTo[jcprop[jc,p],"Delta"->temp];
jcprop[jc,p,opt],
OddQ[p]&&opt=="Delta",
temp = jcprop[jc,p,"ordetB"];
AppendTo[jcprop[jc,p],"Delta"->temp];
jcprop[jc,p,opt],
opt=="ebol",(* Ikeda-Katrusara,arXiv1602.06617v2;explicit formula for siegel series; page 5 *)
{degB}={"degB"}/.jcprop[jc,p];
deltaB = jcprop[jc,p,"Delta"];
temp = If[OddQ[degB],deltaB,xiB = jcprop[jc,p,"xi"];deltaB-1+xiB^2];
AppendTo[jcprop[jc,p],"ebol"->temp];
jcprop[jc,p,opt],
p==2&&opt =="wcfQ",AppendTo[jcprop[jc,p],"wcfQ"->checkWeakCanonicalFormQ[jc]];jcprop[jc,p,opt],
p==2&&opt =="pofQ",AppendTo[jcprop[jc,p],"pofQ"->checkPreOptimalFormQ[jc]];jcprop[jc,p,opt],
True,Null
]
]
jcpropseq[jc_JC,p_,optlist_List]:=Block[{kC,rr,pofseq,out},
rr=Length[jc];
pofseq = Table[jc[[1;;j]],{j,1,rr}];
out =Table[opt->(jcprop[#,p,opt]&/@pofseq),{opt,optlist}];
out
]
(* odd p *)
jcprop[JC[],p_/;OddQ[p]]:=jcprop[JC[]]={"degB"->0,"udet"->1,"ordetB2"->0,"ordetB"->0,"eps"->1};
jcprop[jc_JC,p_/;OddQ[p]]:=jcprop[jc,p]=Block[{krCr,kr,Cr,B1,shortQ,degB,udet,orderB2,ordetB2,ordetB,eps,degC},
krCr = Last[jc];
{kr,Cr}={Mod[#[[1]],2],#[[2]]}&@krCr;
B1=Drop[jc,-1];
{degB,udet,ordetB2,ordetB,eps}={"degB","udet","ordetB2","ordetB","eps"}/.jcprop[B1,p];
degB+=1;
eps =eps*HilbertSymbol[udet*p^ordetB2,p^kr Cr[[1]],p];
udet=Mod[udet*Cr[[1]],p];
ordetB2=Mod[ordetB2+kr,2];
ordetB = ordetB+krCr[[1]];
{"degB"->degB,"udet"->udet,"ordetB2"->ordetB2,"ordetB"->ordetB,"eps"->eps}
]


(* determine whether the input is in weak canonical form or pre-optimal form *)
Clear[checkWeakCanonicalFormQ,checkPreOptimalFormQ]
checkWeakCanonicalFormQ[jcomp_JC,printtraceQ_:False]:=If[jcprop[jcomp,2,"shortQ"],
Block[{rr,kC,evenQ,wc,PMvalind,mm,ind,jcdiag,jcs,degB,ordetB2,xiB,optlist,out},
rr=Length[jcomp];
kC=List@@First/@jcomp;
evenQ[x_]:=And@@(MemberQ[{H,Y},#]&/@x);
If[printtraceQ,Print["wc1"]];
wc[1]=OrderedQ[kC,LessEqual];
If[printtraceQ,Print[{wc[1]}]];
PMvalind={};
Do[
mm=jcomp[[j]][[1]];
If[evenQ[jcomp[[j]][[2]]],AppendTo[PMvalind,"even"],AppendTo[PMvalind,"diag"]]
,{j,1,rr}
];
(* wc[2] *)
If[printtraceQ,Print["wc2"]];
If[printtraceQ,Print[{kC,PMvalind}]];
wc[2]=If[printtraceQ,True,wc[1]];ind=1;
While[wc[2]&&ind<=rr-1,
wc[2]=If[
PMvalind[[ind]]=="diag",
(kC[[ind]]<kC[[ind+1]])&&
If[ind>1,
If[kC[[ind-1]]==kC[[ind]],PMvalind[[ind-1]]=="even",True],
True],
True
];
If[printtraceQ,Print[{ind,wc[2]}]];
ind=ind+1;
];
If[printtraceQ,Print["wc3"]];
jcdiag=JC[];
Do[
If[PMvalind[[j]]=="diag",AppendTo[jcdiag,jcomp[[j]]]]
,{j,1,rr}
];
optlist={"kr","degB","ordetB2","xi"};
If[printtraceQ,Print[{jcdiag,jcpropseq[jcdiag,2,optlist]}]];
rr = Length[jcdiag];
jcs = jcpropseq[jcdiag,2,optlist];
{kC,degB,ordetB2,xiB}=optlist/.jcs;
wc[3]=If[printtraceQ,True,wc[2]];ind=1;
While[wc[3]&&ind<=rr-1,
wc[3]=If[(kC[[ind+1]]==(kC[[ind]]+1))&&EvenQ[degB[[ind]]]&&EvenQ[ordetB2[[ind]]],xiB[[ind]]==0,True];
If[printtraceQ,Print[{ind,wc[3]}]];
ind=ind+1;
];
out = If[printtraceQ,Print[{wc[1],wc[2],wc[3]}];And@@{wc[1],wc[2],wc[3]},wc[3]];
out
],False]
checkPreOptimalFormQ[pof_JC,printtraceQ_:False]:=If[jcprop[pof,2,"shortQ"],
Block[{rr,PMvalind,mm,minmaxm,degather,PO,ind,jindm,degC,sel,ijpairs,ss,degB,xiB,ordetB,kseq,jcdiag,optlist,val},
rr=Length[pof];
{kseq,degC,degB,ordetB,xiB}=({"kr","degC","degB","ordetB2","xi"}/.jcpropseq[pof,2,{"kr","degC","degB","ordetB2","xi"}]);
PMvalind={};
Do[
mm=pof[[j]][[1]];
If[MemberQ[{{H},{Y}},pof[[j]][[2]]],AppendTo[PMvalind,{"even",mm}],AppendTo[PMvalind,{"diag",mm}]]
,{j,1,rr}
];
If[printtraceQ,Print[PMvalind]];
(* PO[1] *)
If[printtraceQ,Print["PO1"]];
minmaxm={Min[#],Max[#]}&@(First/@pof);
degather=GatherBy[Transpose@{Range[rr],PMvalind},#[[2]]&];
If[printtraceQ,Print[degather]];
PO[1]=True;ind=minmaxm[[1]];
While[PO[1]&&minmaxm[[1]]<=ind<=minmaxm[[2]],
jindm=If[sel=Select[degather,#[[1]][[2]]=={"diag",ind}&];sel=={},{},First@sel];
PO[1]=If[jindm=={},True,Total[Part[degC,First/@(jindm)]]<=2];
ind=ind+1
];
ind=minmaxm[[1]];
While[PO[1]&&minmaxm[[1]]<=ind<=minmaxm[[2]],
jindm=If[sel=Select[degather,#[[1]][[2]]=={"even",ind}&];sel=={},{},First@sel];
jindm=Sort[First/@(jindm)];
PO[1]=If[jindm=={},True,jindm==Range[Min[jindm],Max[jindm]]];
ind=ind+1
];
(* PO[2] *)
If[printtraceQ,Print["PO2"]];
ijpairs=Subsets[Range[rr],{2}];
PO[2]=If[printtraceQ,True,PO[1]];ind=1;
While[PO[2]&&ind<=Length[ijpairs],
ss=ijpairs[[ind]];
PO[2]=Which[
{First@PMvalind[[ss[[1]]]],First@PMvalind[[ss[[2]]]]}=={"diag","diag"},(Last@PMvalind[[ss[[1]]]])<= (Last@PMvalind[[ss[[2]]]]),
{First@PMvalind[[ss[[1]]]],First@PMvalind[[ss[[2]]]]}=={"even","even"},(Last@PMvalind[[ss[[1]]]])<= (Last@PMvalind[[ss[[2]]]]),
{First@PMvalind[[ss[[1]]]],First@PMvalind[[ss[[2]]]]}=={"diag","even"},(Last@PMvalind[[ss[[1]]]])<= (Last@PMvalind[[ss[[2]]]])-1,
{First@PMvalind[[ss[[1]]]],First@PMvalind[[ss[[2]]]]}=={"even","diag"},(Last@PMvalind[[ss[[1]]]])<= (Last@PMvalind[[ss[[2]]]])+1
];
If[printtraceQ,Print[{ss,PO[2]}]];
ind=ind+1
];
(* PO[3] *)
PO[3]=If[printtraceQ,True,PO[2]];ind=1;
If[printtraceQ,Print["PO3"]];
While[PO[3]&&ind<=rr,
If[printtraceQ,Print[{ind,PMvalind[[ind]],degC[[ind]],PO[3]}]];
PO[3]=If[
First[PMvalind[[ind]]]=="diag"&&degC[[ind]]==2,ind>=2&&Or[
(*PO3(1) *)
If[printtraceQ,Print[{degB[[ind]],xiB[[ind]],xiB[[ind-1]]}]];
EvenQ[degB[[ind]]]&&xiB[[ind]]==0&&xiB[[ind-1]]==0,
If[printtraceQ,Print[{degB[[ind]],ordetB[[ind-1]],kseq[[ind]]}]];
(*PO3(2) *) 
OddQ[degB[[ind]]]&&EvenQ[ordetB[[ind-1]]+kseq[[ind]]]
],
True];
ind=ind+1
];
(* PO[4] *)
PO[4]=If[printtraceQ,True,PO[3]];ind=2;
If[printtraceQ,Print["PO4"]];
While[PO[4]&&ind<=rr,
If[printtraceQ,Print[{ind,PMvalind[[ind]],degC[[ind]],PO[4]}]];
PO[4]=If[
kseq[[ind]]==(kseq[[ind-1]]-1)&&First[PMvalind[[ind]]]=="diag"&&First[PMvalind[[ind-1]]]=="even", Or[
(*PO4(0) *)
If[printtraceQ,Print[{"PO4(0)",degC[[ind]]}]];
(* check this condition again!! *)
(degC[[ind]]==2),
(*
(degC[[ind]]==2)&&Not[EvenQ[degB[[ind]]]&&EvenQ[ordetB[[ind]]]]&&Not[OddQ[degB[[ind]]]&&(xiB[[ind-1]]==0)],
*)
(*PO4(1) *)
If[printtraceQ,Print[{"PO4(1)",degC[[ind]], degB[[ind]],ordetB[[ind]]}]];
(degC[[ind]]==1)&&EvenQ[degB[[ind]]]&&EvenQ[ordetB[[ind]]],
(*PO4(2) *)
If[printtraceQ,Print[{"PO4(2)",degB[[ind]],xiB[[ind-1]]}]];
(degC[[ind]]==1)&&OddQ[degB[[ind]]]&&(xiB[[ind-1]]==0)
],True];
ind=ind+1
];
(* PO[5] *)
PO[5]=If[printtraceQ,True,PO[4]];ind=1;
If[printtraceQ,Print["PO5"]];
While[PO[5]&&ind<=rr-1,
If[printtraceQ,Print[{ind,PMvalind[[ind]],degC[[ind]],PO[5]}]];
PO[5]=If[
kseq[[ind]]==(kseq[[ind+1]]-1)&&First[PMvalind[[ind]]]=="diag"&&First[PMvalind[[ind+1]]]=="even", degC[[ind]]==1&&Or[
(*PO5(1) *)
If[printtraceQ,Print[{degB[[ind]],ordetB[[ind]]}]];
EvenQ[degB[[ind]]]&&OddQ[ordetB[[ind]]],
If[printtraceQ,Print[{degB[[ind]],xiB[[ind-1]]}]];
(*PO5(2) *) 
OddQ[degB[[ind]]]&&If[ind>=2,xiB[[ind-1]]!=0,True]
],
True];
ind=ind+1
];
(* PO[6] *)
PO[6]=If[printtraceQ,True,PO[5]];
If[printtraceQ,Print["PO6"]];
jcdiag=JC[];
Do[
If[(First@PMvalind[[j]])=="diag",AppendTo[jcdiag,pof[[j]]]]
,{j,1,rr}
];
optlist={"kr","degB","xi"};
If[printtraceQ,Print[{jcdiag,jcpropseq[jcdiag,2,optlist]}]];
rr = Length[jcdiag];
{kseq,degB,xiB}=optlist/.jcpropseq[jcdiag,2,optlist];
ind=1;
While[PO[6]&&ind<=rr-1,
PO[6]=If[(kseq[[ind+1]]==(kseq[[ind]]+1))&&EvenQ[degB[[ind]]],xiB[[ind]]==0,True];
If[printtraceQ,Print[{ind,PO[6]}]];
ind=ind+1;
];
(* Output *)
val = If[printtraceQ,Print[{PO[1],PO[2],PO[3],PO[4],PO[5],PO[6]}];And@@{PO[1],PO[2],PO[3],PO[4],PO[5],PO[6]},PO[6]];
val
],False]


(* diagonalization over Zp *)
(* adapted from the code written by Poor, Shurman and Yuen *)
BlockMatrix[x___]:=ArrayFlatten[x];
MyMinEntry[m_]:=Module[{ans,i,j,x},
ans={1,1};x=m[[1,1]];
Do[If[m[[i,i]]<x,x=m[[i,i]];ans={i,i}],{i,1,Length[m]}];
Do[If[m[[i,j]]<x,x=m[[i,j]];ans={i,j}],{i,1,Length[m]-1},{j,i+1,Length[m]}];
ans
];
ElementaryMatrix1[n_,i_,j_]:=Module[{a},
a=IdentityMatrix[n];
a[[i,i]]=0;a[[j,j]]=0;
a[[i,j]]=1;a[[j,i]]=1;
a
]
ElementaryMatrix3[n_,i_,j_,alp_]:=Module[{a},
a=IdentityMatrix[n];
a[[i,j]]=alp;
a
]
reduceJordanZp[B_List,p_/;PrimeQ[p],printtraceQ_:False]:=Block[{Btemp=B,bijval,i,j,n=Length[B],minv,minij,Em,B1,X,B0,subsize,classifier},
classifier[bb_List]:=Block[{d,a,c,r},
a=Det[bb];d= Length[bb];r=Valuation[a,p]/d;
c=a/p^(d*r);c=Numerator[c]*Denominator[c];
Which[
OddQ[p]&&d==1,c=Mod[c,p];{r,c},
p==2&&d==1,c=Mod[c,8];{r,c},
p==2&&d==2,c=Mod[c,8];
Which[
c==7,{r+1,H},
c==3,{r+1,Y},
True,"error"]
,
True,"error"]
];
(* check valuations *)
bijval=Table[Valuation[Btemp[[i,j]],p],{i,1,n},{j,1,n}];
minij=MyMinEntry[bijval];
If[printtraceQ,Print[{"init:",Btemp//MatrixForm,bijval//MatrixForm,minij}]];
(* step 0 : make Subscript[b, 1j] has min. val. *)
If[minij[[1]]!=1,
Em=ElementaryMatrix1[n,1,minij[[1]]];
Btemp=Em.Btemp.Transpose[Em];
bijval=Table[Valuation[Btemp[[i,j]],p],{i,1,n},{j,1,n}];
minij=MyMinEntry[bijval];
If[printtraceQ,Print[{"e1:",Em//MatrixForm,Btemp//MatrixForm,bijval//MatrixForm,minij}]];
];
(* step 1 : make Subscript[b, 11] or Subscript[b, 12] has min. val. *)
If[minij[[2]]==1,subsize =1;Goto["step3"]];
If[printtraceQ,Print[{"step1"}]];
If[minij[[2]]!=2,
Em=ElementaryMatrix1[n,2,minij[[2]]];
Btemp=Em.Btemp.Transpose[Em];
bijval=Table[Valuation[Btemp[[i,j]],p],{i,1,n},{j,1,n}];
minij=MyMinEntry[bijval];
If[printtraceQ,Print[{"e1:",Em//MatrixForm,Btemp//MatrixForm,bijval//MatrixForm,minij}]];
];
(* step 2 : if p is odd, make Subscript[b, 11] have min. val. *)
If[printtraceQ,Print[{"step2"}]];
If[p!=2,
Em=ElementaryMatrix3[n,1,2,1];
Btemp=Em.Btemp.Transpose[Em];
bijval=Table[Valuation[Btemp[[i,j]],p],{i,1,n},{j,1,n}];
minij=MyMinEntry[bijval];
subsize =1;
If[printtraceQ,Print[{"e3:",Em//MatrixForm,Btemp//MatrixForm,bijval//MatrixForm,minij}]];,
(* p\[Equal]2 *)
subsize =2;If[printtraceQ,Print[{"p=2; nothing to do"}]];
];
(* step 3 : split into two diagonal submatrices *)
Label["step3"];
If[printtraceQ,Print[{"step3:","subsize: "<>ToString[subsize]}]];
B0=Btemp[[1;;subsize,1;;subsize]];
If[n>subsize,
X=Btemp[[1+subsize;;-1,1;;subsize]];
If[printtraceQ,Print[{B0//MatrixForm,X//MatrixForm,Length[X]}]];
Em=BlockMatrix[{{IdentityMatrix[subsize],ConstantArray[0,{subsize,n-subsize}]},{-X.Inverse[B0],IdentityMatrix[n-subsize]}}];
Btemp=Em.Btemp.Transpose[Em];
B1=Btemp[[1+subsize;;-1,1+subsize;;-1]];
If[printtraceQ,Print[{Btemp//MatrixForm,"upper-part:",B0//MatrixForm,"lower-part:",B1}]];
Return[Prepend[reduceJordanZp[B1,p,printtraceQ],classifier[B0]]]
,
(* when B0=Btemp *)
Return[FJC[classifier[B0]]]]
]
(* diagonalize over Qp *)
reduceJordanK[mx_,printtraceQ_:False]:=Block[{m=mx,n=Length[mx],diag,fnzp,Em, m2,Emprod},
If[printtraceQ,Emprod=IdentityMatrix[n]];
If[n==1,Return[First[mx]]];
(* step 0 : find non-zero diagonal *)
Label["step0"];
diag = Diagonal[m];
fnzp=FirstPosition[diag,j_ /; j!=0];
If[fnzp==Missing["NotFound"],Goto["step1"]];
Em=ElementaryMatrix1[n,1,fnzp[[1]]];
m=Em.m.Em;
If[printtraceQ,Emprod=Em.Emprod;Print[{"step1", fnzp,Em//MatrixForm,m//MatrixForm}]];
Goto["step2"];
(* step1 : all diagonals are zero now; find the first non-zero non-diagonal, and use this to make b11 non-zero *)
Label["step1"];
fnzp = FirstPosition[m,j_ /; j!=0];
If[fnzp==Missing["NotFound"],If[printtraceQ,Print["zero matrix"]];Return[ConstantArray[0,n]]];
If[fnzp[[1]]!=1,
Em=ElementaryMatrix1[n,1,fnzp[[1]]];
m=Em.m.Em;
If[printtraceQ,Emprod=Em.Emprod;Print[{"step11",fnzp, Em//MatrixForm,m//MatrixForm}]];
];
Em=ElementaryMatrix3[n,1,fnzp[[2]],1];
m=Em.m.Transpose[Em];
If[printtraceQ,Emprod=Em.Emprod;Print[{"step12",fnzp, Em//MatrixForm,m//MatrixForm}]];
(* step 2 : b11 should be non-zero by now *)
Label["step2"];
Do[
Em=ElementaryMatrix3[n,j,1,-m[[1,j]]/m[[1,1]]];
m=Em.m.Transpose[Em];
If[printtraceQ,Emprod=Em.Emprod;Print[{"step2", {1,j},Em//MatrixForm,m//MatrixForm}]];
,{j,2,n}
];
m2=m[[2;;-1,2;;-1]];
m2=reduceJordanK[m2,printtraceQ];
m=Prepend[m2,m[[1,1]]];
m
]


(* watson decomposition of a matrix *)
Clear[reduceWatson]
WatsonTernary[diag_List]:=
Which[
diag=={1,1,1},{3,2Y},
diag=={1,1,3},{5,2H},
diag=={1,1,5},{7,2Y},
diag=={1,1,7},{1,2H},
diag=={1,3,3},{7,2H},
diag=={1,3,5},{1,2H},
diag=={1,3,7},{3,2H},
diag=={1,5,5},{3,2Y},
diag=={1,5,7},{5,2H},
diag=={1,7,7},{7,2H},
diag=={3,3,3},{1,2Y},
diag=={3,3,5},{3,2H},
diag=={3,3,7},{5,2Y},
diag=={3,5,5},{5,2H},
diag=={3,5,7},{7,2H},
diag=={3,7,7},{1,2Y},
diag=={5,5,5},{7,2Y},
diag=={5,5,7},{1,2H},
diag=={5,7,7},{3,2H},
diag=={7,7,7},{5,2Y}
]
WatsonSplit[initial_List]:=Block[{head,tail,triple,dyy,countH,countY},
(* initial={5,3,7,5,2Y,1,5,7,5,5,1,7,5,7,7,5,3,5,5,5,3,2H};*)
head=Select[initial,NumberQ];
tail=Select[initial,NumberQ[#]==False&];
While[
Length[head]>=3,
triple=Sort[Take[head,3]];head=Drop[head,3];
dyy = WatsonTernary[triple];
PrependTo[head,dyy[[1]]];AppendTo[tail,dyy[[2]]];
{head,tail}
];
head = Sort[head];
countH=Count[tail,2H];
countY=Count[tail,2Y];
countH=countH+2Quotient[countY,2];
countY=Mod[countY,2];
tail = Join[ConstantArray[2H,countH],ConstantArray[2Y,countY]];
{head,tail}
]
reduceWatson[mat_List,printtraceQ_:False]:=Block[{p=2,fjc},
fjc=reduceJordanZp[mat,p,printtraceQ];
reduceWatson[fjc,printtraceQ]
]
reduceWatson[jc_JC,printtraceQ_:False]:=Block[{fjc},
fjc = getFJCfromJC@jc;
reduceWatson[fjc,printtraceQ]
]
reduceWatson[fjc_FJC,printtraceQ_:False]:=Block[{temp,out={}},
temp=List@@fjc;
(* replacement (r,K)\[Rule](r-1,2K) for K= H or Y *)
temp=If[NumberQ[#[[2]]],{#[[1]],#[[2]]},{#[[1]]-1,2#[[2]]}]&/@temp;
temp=Map[{#[[1,1]],(Last/@#)}&,GatherBy[temp,First]];
temp = SortBy[temp,First];
If[printtraceQ,Print[temp]];
temp=Map[{#[[1]],WatsonSplit[#[[2]]]}&,temp];
If[printtraceQ,Print[temp]];
Do[
If[Not[ss[[2]][[1]]=={}],AppendTo[out,{ss[[1]],ss[[2]][[1]]}]];
If[Not[ss[[2]][[2]]=={}],AppendTo[out,{ss[[1]]+1,ss[[2]][[2]]/2}]];
,{ss,temp}
];
JC@@out
]


(* new codes to compute WCF *)
Clear[reduceWeakCanonical]
oddityfusion[cc_List]:=cc/.{1->7,3->5,5->3,7->1};
signwalk[cc_List]:=cc/.{1->3,3->1,5->7,7->5};
(* input: List, output: jc *)
reduceWeakCanonical[mat_List,printtraceQ_:False]:=Block[{jc,wcf},
jc=reduceWatson[mat,printtraceQ];
wcf=reduceWeakCanonical[jc,printtraceQ];
wcf
]
(* input: jc, output: jc *)
reduceWeakCanonical[jcomp_JC,printtraceQ_:False]:=Block[{fjc,wcf},
fjc=getFJCfromJC[jcomp];
wcf=reduceWeakCanonical[fjc,printtraceQ];
getWJCfromFJC[wcf]
]
(* input: fjc, output:fjc *)
reduceWeakCanonical[flatjcomp_FJC,printtraceQ_:False]:=Block[{wdec,evendec,dim,ordtemp,cctemp,funcord,ki,Ji,condQ,ccc,eee,trirep,sol,outval},
(* input must be short, i.e., jcprop[getWJCfromFJC[flatjcomp],2,"shortQ"] True *)
wdec=Select[flatjcomp,NumberQ[#[[2]]]&];
evendec=Select[flatjcomp,Not[NumberQ[#[[2]]]]&];
If[printtraceQ,wdec//Print];
dim=Length[wdec];
ordtemp=0;
cctemp=1;
funcord[x_]:=If[NumberQ[x],0,-2];
Do[
ki[-1]=wdec[[ind-1]][[1]];
ki[0]=wdec[[ind]][[1]];
ki[1]=wdec[[ind+1]][[1]];
Ji[-1]=wdec[[ind-1]][[2]];
Ji[0]=wdec[[ind]][[2]];
Ji[1]=wdec[[ind+1]][[2]];
condQ =(ki[1]==1+ki[0])&&EvenQ[ordtemp+ki[-1]+ki[0]];
If[condQ,
(* apply sign walk *)
If[chip[(-1)^(ind/2)*cctemp*Ji[-1]*Ji[0],2]!=0,
If[Mod[Ji[0],4]==Mod[Ji[1],4](* need signwalk *),
{Ji[0],Ji[1]}=signwalk[{Ji[0],Ji[1]}];
If[printtraceQ,Print[{"signwalk :",wdec,ind->{ki[0],Ji[0]},ind+1->{ki[1],Ji[1]}}]];
wdec=ReplacePart[wdec,{{ind,2}->Ji[0],{ind+1,2}->Ji[1]}]
]
];(* apply oddity fusion *)
If[chip[(-1)^(ind/2)*cctemp*Ji[-1]*Ji[0],2]!=0,
If[Mod[Ji[0],4]!=Mod[Ji[1],4],
{Ji[0],Ji[1]}=oddityfusion[{Ji[0],Ji[1]}];
If[printtraceQ,Print[{"oddityfusion :",wdec,ind->{ki[0],Ji[0]},ind+1->{ki[1],Ji[1]}}]];
wdec=ReplacePart[wdec,{{ind,2}->Ji[0],{ind+1,2}->Ji[1]}]
]
];
];
ordtemp+=ki[-1]+ki[0];
cctemp=Mod[cctemp*Ji[-1]*Ji[0],8];
;
,{ind,2,dim-1,2}
];
outval = SortBy[Join[wdec,evendec],{First,funcord[#[[2]]]&}];
outval
]


Clear[reducePreOptimal]
(* functions for reducePreOptimal *)
(* kJtype : classifies : u1, u1+u2, K1+...+Km *)
kJtype[wcf_FJC]:=Block[{nn,string},
string=Last/@wcf;
nn=Length[string];
Which[
nn==1&&NumberQ[string[[-1]]],"u1",
nn==2&&NumberQ[string[[-1]]]&&NumberQ[string[[-2]]],"u1u2",
True,"K"]
]
separateLast[jc0_JC]:=Block[{jc,classifier,temp,kr,type,Jr={}},
jc=List@@jc0;
classifier[arg_]:=If[MemberQ[{{H},{Y}},arg],"K","N"];
type =classifier[Last[jc][[2]]];
If[type=="K",
kr=Last[jc][[1]];
temp=jc;
While[temp!={}&&kr==Last[temp][[1]]&&("K"==classifier[Last[temp][[2]]]),
PrependTo[Jr,Last[temp]];
temp=Drop[temp,-1];
];{JC@@temp,getFJCfromJC[JC@@Jr]},{JC@@Drop[jc,-1],getFJCfromJC@JC[Last[jc]]}]
]
(* input : weak canonical form *)
reducePreOptimal[fjc_FJC,printtraceQ_:False]:=reducePreOptimal[getWJCfromFJC[fjc],printtraceQ]
reducePreOptimal[wcf_JC,printtraceQ_:False]:=Block[{rr,nn,B1,kr,BmkrJr,krJr,Jr,krminus1Jrminus1,krminus1,Jrminus1,u1,u2,Brminus1,Brminus2,pocseq,p=2},
(* input must be a weak-canonical form; jcprop[wcf,2,"wcfQ"] True *)
(* generate and return pocseq *)
nn=jcprop[wcf,p,"degB"];
rr=Length[wcf];
If[nn==0,pocseq=wcf;Goto["finish"]];
{BmkrJr,krJr}=separateLast[wcf];
Which[
kJtype[krJr]=="u1",Goto["case1"],
kJtype[krJr]=="u1u2",Goto["case2"],
kJtype[krJr]=="K"&&UnsameQ[BmkrJr,JC[]],Goto["case3"],
kJtype[krJr]=="K"&&SameQ[BmkrJr,JC[]],Goto["case4"]
];
Label["case1"];
If[printtraceQ,Print["case1"]];
kr = krJr[[1]][[1]];
Jr={krJr[[1]][[2]]};
B1=BmkrJr;
pocseq =Append[reducePreOptimal[B1,printtraceQ],{kr,Jr}];
Goto["finish"];
Label["case2"];
If[printtraceQ,Print["case2"]];
kr = krJr[[1]][[1]];
Jr={krJr[[1]][[2]],krJr[[2]][[2]]};
B1=BmkrJr;
If[printtraceQ,Print[{nn,B1}]];
Which[
(EvenQ[nn]&&jcprop[B1,p,"xi"]===0&&jcprop[wcf,p,"xi"]===0)||(OddQ[nn]&&EvenQ[jcprop[B1,p,"ordetB2"]+kr]),Goto["case21"],
True,Goto["case22"]
];
Label["case21"];
If[printtraceQ,Print["case21"]];
pocseq = Append[reducePreOptimal[B1,printtraceQ],{kr,Jr}];
Goto["finish"];
Label["case22"];
If[printtraceQ,Print["case22"]];
If[printtraceQ,B1];
pocseq =Join[reducePreOptimal[B1,printtraceQ],JC[{kr,{Jr[[1]]}},{kr,{Jr[[2]]}}]];
Goto["finish"];
Label["case3"];
If[printtraceQ,Print["case3"]];
{Brminus1,krJr}=separateLast[wcf];
If[Brminus1==={},
Goto["case30"]
];
kr = wcf[[-1]][[1]];
krminus1Jrminus1=separateLast[Brminus1][[2]];
krminus1=krminus1Jrminus1[[1]][[1]];
Which[
kr==krminus1+1&&kJtype[krminus1Jrminus1]=="u1",Goto["case31"],
kr==krminus1+1&&kJtype[krminus1Jrminus1]=="u1u2",Goto["case32"],
kr==krminus1+1&&kJtype[krminus1Jrminus1]=="K",Goto["case33"],
kr>=krminus1+2,Goto["case33"]
];
Label["case30"];
pocseq=Map[{#[[1]],{#[[2]]}}&,krJr];
Goto["finish"];
Label["case31"];
u1=krminus1Jrminus1[[1]][[2]];
If[printtraceQ,Print["case31"]];
Which[
EvenQ[jcprop[Brminus1,p,"degB"]]&&EvenQ[jcprop[Brminus1,p,"ordetB2"]],Goto["case311"],
(* the following is incorrect as confirmed by Katsurada *)
(*
Length[Brminus1]\[GreaterEqual]2&&OddQ[wcfstats[Drop[Brminus1,-1]][[1]]]&&xipwcf[Drop[Brminus1,-1]]\[Equal]0,Goto["case311"],
*)
rr>=3&&OddQ[jcprop[Brminus1,p,"degB"]]&&jcprop[Drop[Brminus1,-1],p,"xi"]==0,Goto["case311"],
True,Goto["case312"]
];
Label["case311"];
If[printtraceQ,Print["case311"]];
B1=Drop[Brminus1,-1];
pocseq =Join[reducePreOptimal[B1,printtraceQ],JC@@Map[{#[[1]],{#[[2]]}}&,krJr],JC[{krminus1,{u1}}]];
Goto["finish"];
Label["case312"];
If[printtraceQ,Print["case312"]];
B1=Drop[Brminus1,-1];
pocseq =Join[reducePreOptimal[B1,printtraceQ],JC[{krminus1,{u1}}],JC@@Map[{#[[1]],{#[[2]]}}&,krJr]];
Goto["finish"];
Label["case32"];
If[printtraceQ,Print["case32"]];
u1=krminus1Jrminus1[[1]][[2]];
u2=krminus1Jrminus1[[2]][[2]];
Brminus2 =Drop[Brminus1,-1];
If[printtraceQ,Print[{Brminus1,Length[Brminus1]}]];
If[printtraceQ,Print[{Brminus2,Length[Brminus2]}]];
Which[
rr==2,Goto["case321a"],
rr>=3&&EvenQ[jcprop[Brminus2,p,"degB"]]&&jcprop[Brminus2,p,"xi"]!=0,Goto["case321b"],
rr>=3&&OddQ[jcprop[Brminus2,p,"degB"]]&&OddQ[jcprop[Brminus2,p,"ordetB2"]+krminus1],Goto["case321c"],
rr>=3&&EvenQ[jcprop[Brminus2,p,"degB"]]&&jcprop[Brminus2,p,"xi"]==0&&jcprop[Brminus1,p,"xi"]==0,Goto["case322a"],
rr>=3&&OddQ[jcprop[Brminus2,p,"degB"]]&&EvenQ[jcprop[Brminus2,p,"ordetB2"]+krminus1],Goto["case322b"],
rr>=3&&EvenQ[jcprop[Brminus2,p,"degB"]]&&jcprop[Brminus2,p,"xi"]==0&&jcprop[Brminus1,p,"xi"]!=0,Goto["case323"]
];
Label["case321a"];
If[printtraceQ,Print["case321a"]];
Goto["case321"];
Label["case321b"];
If[printtraceQ,Print["case321b"]];
Goto["case321"];
Label["case321c"];
If[printtraceQ,Print["case321c"]];
Goto["case321"];
Label["case321"];
B1=Brminus2;
pocseq =Join[reducePreOptimal[B1,printtraceQ],JC[{krminus1,{u1}}],JC@@Map[{#[[1]],{#[[2]]}}&,krJr],JC[{krminus1,{u2}}]];
Goto["finish"];
Label["case322a"];
If[printtraceQ,Print["case322a"]];
Goto["case322"];
Label["case322b"];
If[printtraceQ,Print["case322b"]];
Goto["case322"];
Label["case322"];
If[printtraceQ,Print["case322"]];
B1=Brminus2;
pocseq =Join[reducePreOptimal[B1,printtraceQ],JC@@Map[{#[[1]],{#[[2]]}}&,krJr],JC[{krminus1,{u1,u2}}]];
Goto["finish"];
Label["case323"];
If[printtraceQ,Print["case323"]];
B1=Brminus2;
pocseq =Join[reducePreOptimal[B1,printtraceQ],JC@@Map[{#[[1]],{#[[2]]}}&,krJr],JC[{krminus1,{u1}}],JC[{krminus1,{u2}}]];
Goto["finish"];
Label["case33"];
If[printtraceQ,Print["case33"]];
B1=Brminus1;
pocseq =Join[reducePreOptimal[B1,printtraceQ],JC@@Map[{#[[1]],{#[[2]]}}&,krJr]];
Goto["finish"];
Label["case4"];
If[printtraceQ,Print["case4"]];
pocseq =JC@@Map[{#[[1]],{#[[2]]}}&,krJr];
Goto["finish"];
Label["finish"];
pocseq
]


(* gk invariant *)
Clear[computeGK]
computeGK[mat_List,p_]:=If[p==2,computeGK[reducePreOptimal@reduceWeakCanonical@reduceWatson[mat],p],computeGK[getJCfromFJC@reduceJordanZp[mat,p],p]]
computeGK[pofseq_JC,2,printtraceQ_:False]:=Block[{rr,gktemp={},as,kseq,degC,xifunc,ordetfunc,degB,ordetB,xiB},
(* input must be a pre-optimal form; check by jcprop[pofseq,2,"pofQ"] *)
rr=Length[pofseq];
{kseq,degC,degB,ordetB,xiB}=({"kr","degC","degB","ordetB2","xi"}/.jcpropseq[pofseq,2,{"kr","degC","degB","ordetB2","xi"}]);
ordetfunc[i_]:=If[i==0,0,ordetB[[i]]];
xifunc[i_]:=If[i==0,1,xiB[[i]]];
If[printtraceQ,{kseq,degC,degB,ordetB,xiB}//Print];
Do[
Which[
degC[[ind]]==1,as=If[
OddQ[degB[[ind]]],
Which[
OddQ[ordetfunc[ind-1]],kseq[[ind]]+2,
EvenQ[ordetfunc[ind-1]]&&xifunc[ind-1]==0,kseq[[ind]]+1,
EvenQ[ordetfunc[ind-1]]&&xifunc[ind-1]!=0,kseq[[ind]]
],
(* EvenQ[degB[[ind]]] *)
Which[
OddQ[ordetfunc[ind]],kseq[[ind]],
EvenQ[ordetfunc[ind]]&&xifunc[ind]==0,kseq[[ind]]+1,
EvenQ[ordetfunc[ind]]&&xifunc[ind]!=0,kseq[[ind]]+2
]
];AppendTo[gktemp,as],
degC[[ind]]==2&&NumberQ[pofseq[[ind]][[2]][[1]]],gktemp=Join[gktemp,{kseq[[ind]]+1,kseq[[ind]]+1}],
degC[[ind]]==2,gktemp=Join[gktemp,{kseq[[ind]],kseq[[ind]]}]
]
,{ind,1,rr}
];
gktemp
]
computeGK[jc_JC,p_/;OddQ[p]]:=List@@(First/@jc)


Clear[computeNEGKdatum,checkNEGKdatumQ]
computeNEGKdatum[mat_List,p_]:=If[p==2,computeNEGKdatum[reducePreOptimal@reduceWeakCanonical@reduceWatson[mat],p],computeNEGKdatum[getJCfromFJC@reduceJordanZp[mat,p],p]]
(* p=2 *)
computeNEGKdatum[pofseq_JC,2,printtraceQ_:False]:=Block[{p=2,optlist,gkb,eps,rr,degC,degB,etaseq,xiB,ss},
(* assuming the input is a pre-optimal form *)
(* CIKY Theorem 4.3 *)
optlist = {"degC","degB","xi","eta"};
{degC,degB,xiB,etaseq}=(optlist/.jcpropseq[pofseq,p,optlist]);
If[printtraceQ,{degC,degB,xiB,etaseq}//Print];
gkb=computeGK[pofseq,p];
rr=Length[gkb];
Do[
If[printtraceQ,Print[ind]];
eps[ind]=Which[
ind==1, If[printtraceQ,{"case1"}//Print];1,
EvenQ[ind]&&MemberQ[degB,ind], ss=First@FirstPosition[degB,ind];If[printtraceQ,{"case2",ss,xiB[[ss]]}//Print];xiB[[ss]],
OddQ[ind]&&ind>=3&&MemberQ[degB,ind],If[printtraceQ,{"case3"}//Print];ss=First@FirstPosition[degB,ind];etaseq[[ss]],
OddQ[ind]&&ind>=3&&MemberQ[degB,ind+1]&&(ss=First@FirstPosition[degB,ind+1];degC[[ss]]==2)&&EvenQ[Total[gkb[[1;;ind+1]]]], If[printtraceQ,{"case4"}//Print];etaseq[[ss]]xiB[[ss]]^gkb[[ind]],
EvenQ[ind]&&MemberQ[degB,ind+1]&&(ss=First@FirstPosition[degB,ind+1];degC[[ss]]==2)&&OddQ[Total[gkb[[1;;ind]]]],If[printtraceQ,{"case5"}//Print];0,
ind>=2&&MemberQ[degB,ind+1]&&(ss=First@FirstPosition[degB,ind+1];degC[[ss]]==2)&&OddQ[ind+1+Total[gkb[[1;;2Floor[(ind+1)/2]]]]],If[printtraceQ,{"case6"}//Print];RandomChoice[{-1,1}]
]
,{ind,1,rr}
];
{gkb,Array[eps,rr]}
]
computeNEGKdatum[pofseq_JC,p_/;OddQ[p],printtraceQ_:False]:=Block[{optlist,xiB,etaseq,gkb,rr,eps},
(* IK15; Prop 6.1 *)
optlist = {"xi","eta"};
{xiB,etaseq}=(optlist/.jcpropseq[pofseq,p,optlist]);
If[printtraceQ,{xiB,etaseq}//Print];
gkb=computeGK[pofseq,p];
rr=Length[gkb];
Do[
If[printtraceQ,Print[ind]];
eps[ind]=If[EvenQ[ind],xiB[[ind]],etaseq[[ind]]];
,{ind,1,rr}
];
{gkb,Array[eps,rr]}
]
checkNEGKdatumQ[{gkb_,eps_},printtraceQ_:False]:=Block[{NC,rr,ind,val},
rr=Length[gkb];
NC[1]=True;ind=1;
If[printtraceQ,Print["NC1"]];
While[NC[1]&&ind<=rr-1,
NC[1]=(gkb[[ind]]<= gkb[[ind+1]]);
ind=ind+1
];
If[printtraceQ,Print[NC[1]]];
NC[2]=If[printtraceQ,True,NC[1]];ind=1;
If[printtraceQ,Print["NC2"]];
While[NC[2]&&ind<=rr,
NC[2]=If[EvenQ[ind],
SameQ[eps[[ind]]!=0,EvenQ[Total[gkb[[1;;ind]]]]],
True];
ind=ind+1
];
If[printtraceQ,Print[NC[2]]];
NC[3]=If[printtraceQ,True,NC[2]];ind=1;
If[printtraceQ,Print["NC3"]];
While[NC[3]&&ind<=rr,
NC[3]=If[OddQ[ind],eps[[ind]]!=0,True];
ind=ind+1
];
If[printtraceQ,Print[NC[3]]];
If[printtraceQ,Print["NC4"]];
NC[4]=If[printtraceQ,True,NC[3]];
NC[4]=If[NC[4],(eps[[1]]==1),False];
If[printtraceQ,Print[NC[4]]];
NC[5]=If[printtraceQ,True,NC[4]];ind=1;
If[printtraceQ,Print["NC5"]];
While[NC[5]&&3<=ind<=rr,
NC[5]=If[OddQ[ind]&&EvenQ[Total[gkb[[1;;ind-1]]]],SameQ[eps[[ind]],eps[[ind-2]]eps[[ind-1]]^(gkb[[ind]]+gkb[[ind-1]])],True];
ind=ind+1
];
If[printtraceQ,Print[NC[5]]];
val = If[printtraceQ,Print[{NC[1],NC[2],NC[3],NC[4],NC[5]}];And@@{NC[1],NC[2],NC[3],NC[4],NC[5]},NC[5]];
val
]


(* computing the Siegel series : FpLaurent *)
Clear[FpLaurent]
FpLaurent[{{},eps_},p_,k_Integer]:=1
(*
FpLaurent[{{a1_},{1}},k_Integer]:=FpLaurent[{{a1},{1}},k]=Block[{x=2^(k/2),val},
val = Sum[x^(-a1/2+i),{i,0,a1}];
val//Simplify
]
*)
FpLaurent[{gkb_,eps0_},p_,k_Integer]:=FpLaurent[{gkb,eps0},p,k]=Block[{rr,Crat,Drat,CC,gkbpsum,ebold,xiseq,xiprimeseq,val,eps},
eps = 1@@eps0;
Crat[e1_,e2_,g_,X_]:=p^(e2/4) X^(-(e1-e2)/2-1)*(1-g*p^(-1/2) X)/(X^-1-X);
Drat[e1_,e2_,g_,X_]:=(p^(e2/4) X^(-(e1-e2)/2))/(1-g X);
CC[i_,e1_,e2_,g_,X_]:=If[EvenQ[i],Crat[e1,e2,g,X],Drat[e1,e2,g,X]];
rr=Length[gkb];
gkbpsum=Accumulate[gkb];
ebold=0@@Table[If[OddQ[i],gkbpsum[[i]],2Floor[gkbpsum[[i]]/2]],{i,1,rr}];
xiseq=0@@Table[If[EvenQ[i],eps[[i]],eps[[i-1]]],{i,1,rr}];
(*
zetaseq=Table[If[EvenQ[i],1,eps[[i]]],{i,1,rr}];
val = CC[rr,ebold[[rr]],ebold[[rr-1]],xiseq[[rr]],p^(k/2)]*FpLaurent[{Drop[gkb,-1],Drop[eps,-1]},p,(k+1)]+zetaseq[[rr]]*CC[rr,ebold[[rr]],ebold[[rr-1]],xiseq[[rr]],p^(-k/2)]*FpLaurent[{Drop[gkb,-1],Drop[eps,-1]},p,(-k+1)];
*)
xiprimeseq=Table[If[EvenQ[i],eps[[i-1]],eps[[i]]],{i,1,rr}];
val = CC[rr,ebold[[rr]],ebold[[rr-1]],xiseq[[rr]],p^(k/2)]*FpLaurent[{Drop[gkb,-1],Drop[eps,-1]},p,(k+1)]+xiprimeseq[[rr]]*CC[rr,ebold[[rr]],ebold[[rr-1]],xiseq[[rr]],p^(-k/2)]*FpLaurent[{Drop[gkb,-1],Drop[eps,-1]},p,(k-1)];
val//Simplify
]
computeFpoly[pof_JC,p_,var_]:=Block[{nn,eb,negk,vals},
nn=jcprop[pof,p,"degB"];eb = jcprop[pof,p,"ebol"];
negk=computeNEGKdatum[pof,p];
vals=Table[{p^k,Simplify[(p^((k+(nn+1)/2) eb/2))FpLaurent[negk,p,2k+nn+1]]},{k,0,eb}];
Expand[InterpolatingPolynomial[vals,var]]
]
computeFpoly[mat_List,p_,var_]:=If[p==2,
computeFpoly[reducePreOptimal@reduceWeakCanonical@reduceWatson[mat],p,var],
computeFpoly[getJCfromFJC@reduceJordanZp[mat,p],p,var]]


(* check the functional equation for Fpoly *)
checkFpolyDual[pof_JC,p_]:=Block[{Bdiag,n,H,F,eB,lhs,rhs,X},
eB=jcprop[pof,p,"ebol"];
H=computeNEGKdatum[pof,p];
F=computeFpoly[pof,p,X];
n=Length[H[[1]]];
lhs = F/.{X->p^(-n-1) X^-1};
rhs  =(Times@@{F,(p^((n+1)/2) X)^-eB,If[OddQ[n],Last@H[[2]],1]});
SameQ[lhs/rhs//Simplify,1]
]


(* GK invariant based on Cho-Yamauchi inductive formula; assuming p=2 *)
Clear[computeGKbyCY,computeGK2]
computeGK2[mat_List,printtraceQ_:False]:=computeGK2[reduceWatson[mat],printtraceQ]
computeGK2[jc_JC,printtraceQ_:False]:=computeGK2[getFJCfromJC@jc,printtraceQ]
computeGK2[flatjcomp_FJC,printtraceQ_:False]:=Block[{wdec,evendec,gkdiag,gkeven},
wdec=Select[flatjcomp,NumberQ[#[[2]]]&];
evendec=Select[flatjcomp,Not[NumberQ[#[[2]]]]&];
If[printtraceQ,{wdec,evendec}//Print];
gkdiag=If[UnsameQ[wdec,FJC[]],computeGKbyCY[Transpose@(List@@wdec),printtraceQ],{}];
gkeven=List@@Map[{#[[1]],#[[1]]}&,evendec];
Sort@Flatten@{gkdiag,gkeven}
]
computeGKbyCY[{{},{}}]={};
computeGKbyCY[ecf_List,printtraceQ_:False]:=computeGKbyCY[ecf]=Block[{mu,numlist,mm,diag,gk,nodd,neven,gksub,subec,condQ,sizediff,mutotal,ecCombine},
ecCombine[e_List,c_List]:=c*2^e;
{mu,numlist}=ecf;
mm=Length[mu];
If[mm>3,Goto["large_matrix"],Goto["small_matrix"]];
Label["small_matrix"];
If[printtraceQ,Print["smallmatrix"]];
gk = Which[
mm==1,mu,
mm==2,Which[
OddQ[mu[[1]]-mu[[2]]],mu,
EvenQ[mu[[1]]-mu[[2]]]&&Mod[Total[numlist],4]==2,mu+{0,1},
EvenQ[mu[[1]]-mu[[2]]]&&Mod[Total[numlist],4]==0,mu+{0,2},
True,"error"
],
mm==3,Which[
OddQ[mu[[1]]-mu[[2]]],mu+{0,0,2},
EvenQ[mu[[1]]-mu[[2]]]&&(Mod[numlist[[1]]+numlist[[2]],4]==2||(mu[[3]]==mu[[2]])),mu+{0,1,1},
EvenQ[mu[[1]]-mu[[2]]]&&Mod[numlist[[1]]+numlist[[2]],4]==0&&(mu[[3]]>mu[[2]]),Sort[mu+{0,2,0}],
True,"error"
],
True,"error"
];
Goto["finish"];
Label["large_matrix"];
If[OddQ[mm],nodd=mm-2,nodd=mm-1];
If[EvenQ[mm],neven=mm-2,neven=mm-1];
(* largest proper submatrix of even degree *)
subec[0]={mu[[1;;neven]],numlist[[1;;neven]]};
gksub[0]=computeGKbyCY@subec[0];
(* largest odd size submatrix *)
subec[1]={mu[[1;;nodd]],numlist[[1;;nodd]]};
gksub[1]=computeGKbyCY@subec[1];
(* largest even submatrix of submat[1] *)
subec[2]={mu[[1;;nodd-1]],numlist[[1;;nodd-1]]};
gksub[2]=computeGKbyCY@subec[2];
condQ[thm35]=And@@{EvenQ[Total[gksub[0]]],mu[[neven+1]]>=gksub[0][[neven]]-1};
condQ[thm36]=And@@{gksub[1][[nodd]]==(mu[[nodd]]+1),gksub[1][[nodd-1]]<=mu[[nodd-1]]+1,OddQ[Total[gksub[1][[1;;nodd-1]]]],
If[mu[[nodd-1]]<mu[[nodd]],SameQ[gksub[2],Drop[gksub[1],-1]],True]};
condQ[thm37]=And@@{gksub[1][[nodd]]==(mu[[nodd]]+2),gksub[1][[nodd-1]]<=mu[[nodd]],OddQ[Total[mu[[1;;nodd-1]]]],SameQ[gksub[2],Drop[gksub[1],-1]]};
If[OddQ[mm],condQ[thm99]=And@@{EvenQ[Total[gksub[2]]]}];
Which[
condQ[thm35],Goto["thm35"],
condQ[thm36],Goto["thm36"],
condQ[thm37],Goto["thm37"],
condQ[thm99],Goto["thm99"],
True,"error"
];
Label["thm35"];
If[printtraceQ,Print["thm35"]];
gk = Sort[Join[gksub[0],computeGKbyCY@{mu[[neven+1;;mm]],numlist[[neven+1;;mm]]}]];
Goto["finish"];
Label["thm36"];
If[printtraceQ,Print["thm36"]];
mutotal = Total[mu[[1;;nodd+1]]];
subec[3]={mu[[1;;nodd+1]],numlist[[1;;nodd+1]]};
gk = Which[
(* 1a *)
mu[[nodd+1]]==mu[[nodd]]&&EvenQ[mutotal]&&(xip[ecCombine@@{mu[[1;;nodd+1]],numlist[[1;;nodd+1]]},2]==0),
If[printtraceQ,Print["1a"]];
If[mm-nodd==1,Join[gksub[1],{mu[[nodd+1]]+1}],Join[gksub[1],{mu[[nodd+1]]+1,mu[[nodd+2]]+1}]],
(* 1b *)
mu[[nodd+1]]==mu[[nodd]]&&EvenQ[mutotal]&&(xip[ecCombine@@{mu[[1;;nodd+1]],numlist[[1;;nodd+1]]},2]!= 0),
If[printtraceQ,Print["1b"]];
If[mm-nodd==1,Join[gksub[1],{mu[[nodd+1]]+2}],Join[gksub[1],{mu[[nodd+1]]+2},{mu[[nodd+2]]}]],
(* 2a *)
mu[[nodd+1]]>mu[[nodd]]&&OddQ[mutotal],
If[printtraceQ,Print["2a"]];
If[mm-nodd==1,Join[gksub[1],{mu[[nodd+1]]}],Join[gksub[1],{mu[[nodd+1]],mu[[nodd+2]]+2}]],
(* 2b *)
mu[[nodd+1]]>mu[[nodd]]&&EvenQ[mutotal]&&(xip[(ecCombine@@subec[3]),2]==0),
If[printtraceQ,Print["2b"]];
If[mm-nodd==1,Join[gksub[1],{mu[[nodd+1]]+1}],Join[gksub[1],{mu[[nodd+1]]+1,mu[[nodd+2]]+1}]],
(* 2c *)
mu[[nodd+1]]>mu[[nodd]]&&EvenQ[mutotal]&&(xip[(ecCombine@@subec[3]),2]!= 0),
If[printtraceQ,Print["2c"]];
If[mm-nodd==1,Join[gksub[1],{mu[[nodd+1]]+2}],
If[mu[[nodd+2]]>=mu[[nodd+1]]+1,Join[gksub[1],{mu[[nodd+1]]+2,mu[[nodd+2]]}],Join[gksub[1],{mu[[nodd+1]]+1,mu[[nodd+2]]+1}]]
],
True,"error"
];
Goto["finish"];
Label["thm37"];
If[printtraceQ,Print["thm37"]];
mutotal = Total[mu[[1;;nodd+1]]];
subec[3]={mu[[1;;nodd+1]],numlist[[1;;nodd+1]]};
gk = Which[
(* 1 *)
mu[[nodd+1]]==mu[[nodd]]&&OddQ[mutotal],
If[printtraceQ,Print["1"]];
If[mm-nodd==1,Join[Drop[gksub[1],-1],{mu[[nodd]]+1,mu[[nodd]]+1}],Join[Drop[gksub[1],-1],{mu[[nodd]]+1,mu[[nodd]]+1,mu[[nodd+2]]+2}]],
(* 2a *)
mu[[nodd+1]]==(mu[[nodd]]+1)&&EvenQ[mutotal]&&(xip[(ecCombine@@subec[3]),2]== 0),
If[printtraceQ,Print["2a"]];
If[mm-nodd==1,
If[printtraceQ,Print["2a1"]];Join[Drop[gksub[1],-1],{mu[[nodd]]+2,mu[[nodd+1]]+1}],
If[printtraceQ,Print["2a2"]];Join[Drop[gksub[1],-1],{mu[[nodd]]+2,mu[[nodd+1]]+1,mu[[nodd+2]]+1}]],
(* 2b *)
mu[[nodd+1]]==(mu[[nodd]]+1)&&EvenQ[mutotal]&&(xip[(ecCombine@@subec[3]),2]!= 0),
If[printtraceQ,Print["2b"]];
If[mm-nodd==1,Join[Drop[gksub[1],-1],{mu[[nodd]]+2,mu[[nodd+1]]+2}],
If[
mu[[nodd+2]]>=mu[[nodd+1]]+1,Sort@Join[Drop[gksub[1],-1],{mu[[nodd]]+2,mu[[nodd+1]]+2,mu[[nodd+2]]}],Join[Drop[gksub[1],-1],{mu[[nodd]]+2,mu[[nodd+1]]+1,mu[[nodd+2]]+1}]
]
],
(* 3a *)
mu[[nodd+1]]>=(mu[[nodd]]+2)&&OddQ[mutotal],
If[printtraceQ,Print["3a"]];
If[mm-nodd==1,Join[gksub[1],{mu[[nodd+1]]}],Join[gksub[1],{mu[[nodd+1]],mu[[nodd+2]]+2}]],
(* 3b *)
mu[[nodd+1]]>=(mu[[nodd]]+2)&&EvenQ[mutotal]&&(xip[(ecCombine@@subec[3]),2]== 0),
If[printtraceQ,Print["3b"]];
If[mm-nodd==1,Join[gksub[1],{mu[[nodd+1]]+1}],Join[gksub[1],{mu[[nodd+1]]+1,mu[[nodd+2]]+1}]],
(* 3c *)
mu[[nodd+1]]>= (mu[[nodd]]+2)&&EvenQ[mutotal]&&(xip[(ecCombine@@subec[3]),2]!= 0),
If[printtraceQ,Print["3c"]];
If[mm-nodd==1,Join[gksub[1],{mu[[nodd+1]]+2}],
If[
mu[[nodd+2]]>=mu[[nodd+1]]+1,
Sort@Join[gksub[1],{mu[[nodd+1]]+2,mu[[nodd+2]]}],
Join[gksub[1],{mu[[nodd+1]]+1,mu[[nodd+2]]+1}]
]
],
True,"error"
];
Goto["finish"];
Label["thm99"];
gk = Sort[Join[gksub[2],computeGKbyCY@{mu[[nodd;;mm]],numlist[[nodd;;mm]]}]];
Goto["finish"];
Label["finish"];
gk
]


(* arithmetic intersection number *)
QpTernaryIsotropicQ[Q_List,p_]:=QpTernaryIsotropicQ[Q,p]=Block[{diag,val,a,b,c},
(* Cassels;Lemma 4.2.5 *)
If[Length[Q]==3&&PrimeQ[p],
{a,b,c}=reduceJordanK[Q];
val = HilbertSymbol[-a c,-b c,p];
Which[
val==1,True,
val==-1,False,
True,Print["error"];"error"
]]
]
GrossKeatingInv[Qmat_,prime_]:=Block[{ext,gk},
{gk,ext} = {#[[1]],#[[2]][[2]]}&@computeNEGKdatum[Qmat,prime];
ext =If[EvenQ[gk[[1]]+gk[[2]]]&&gk[[2]]<gk[[3]],ext,Null];
{gk,ext}
]
(*
GrossKeatingInv[Qmat_,prime_/;OddQ[prime]]:=Block[{jc,triple,eee,uuu,extgk},
jc =reduceWatson[Qmat,prime];
eee =computeGK[jc,prime];
uuu =Flatten[List@@(#[[2]]&/@jc)];
extgk = If[EvenQ[eee[[1]]+eee[[2]]]&&eee[[2]]<eee[[3]],JacobiSymbol[-uuu[[1]]*uuu[[2]],prime],0];
{eee,extgk}
]
*)
GrossKeatingAlpha[Qmat_,prime_]:=Block[{gkB,aaa},
gkB= GrossKeatingInv[Qmat,prime];
aaa = gkB[[1]];
If[
EvenQ[aaa[[1]]+aaa[[2]]],Sum[(i+1)(Total[aaa]-3i)prime^i,{i,0,aaa[[1]]-1}]+Sum[(aaa[[1]]+1)(aaa[[1]]+Total[aaa]-4i)prime^i,{i,aaa[[1]],(aaa[[1]]+aaa[[2]]-2)/2}]+(aaa[[1]]+1)/2 (aaa[[3]]-aaa[[2]]+1)prime^((aaa[[1]]+aaa[[2]])/2),
Sum[(i+1)(Total[aaa]-3i)prime^i,{i,0,aaa[[1]]-1}]+Sum[(aaa[[1]]+1)(aaa[[1]]+Total[aaa]-4i)prime^i,{i,aaa[[1]],(aaa[[1]]+aaa[[2]]-1)/2}]
]
]/;QpTernaryIsotropicQ[Qmat,prime]==False
GrossKeatingBeta[Qmat_,lprime_]:=Block[{gkB,aaa,extgk},
gkB= GrossKeatingInv[Qmat,lprime];
aaa = gkB[[1]];
extgk = gkB[[2]];
Which[
EvenQ[aaa[[1]]+aaa[[2]]]&&(extgk==1||aaa[[2]]==aaa[[3]]),Sum[2(i+1)lprime^i,{i,0,aaa[[1]]-1}]+Sum[2(aaa[[1]]+1)lprime^i,{i,aaa[[1]],(aaa[[1]]+aaa[[2]]-2)/2}]+(aaa[[1]]+1)(aaa[[3]]-aaa[[2]]+1)lprime^((aaa[[1]]+aaa[[2]])/2),
EvenQ[aaa[[1]]+aaa[[2]]]&&extgk==-1,Sum[2(i+1)lprime^i,{i,0,aaa[[1]]-1}]+Sum[2(aaa[[1]]+1)lprime^i,{i,aaa[[1]],(aaa[[1]]+aaa[[2]]-2)/2}]+(aaa[[1]]+1)lprime^((aaa[[1]]+aaa[[2]])/2),
OddQ[aaa[[1]]+aaa[[2]]],Sum[2(i+1)lprime^i,{i,0,aaa[[1]]-1}]+Sum[2(aaa[[1]]+1)lprime^i,{i,aaa[[1]],(aaa[[1]]+aaa[[2]]-1)/2}]
]
]/;QpTernaryIsotropicQ[Qmat,lprime]
GKcontrib[Qmat_,prime_]:=Block[{\[CapitalDelta],lset,prod},
(* p.228 of Gross-Keating for the definition of the determinant of a quadratic form*)
\[CapitalDelta]=4Det[Qmat];
lset = First/@FactorInteger[\[CapitalDelta]];
lset =Select[ First/@FactorInteger[\[CapitalDelta]],#!=prime&];
prod=Times@@(GrossKeatingBeta[Qmat,#]&/@lset);
prod*GrossKeatingAlpha[Qmat,prime]
]
QpTernaryAnisotropicPrimes[Qmat_List]:=QpTernaryAnisotropicPrimes[Qmat]=Block[{diag,pfactors},
diag = reduceJordanK[Qmat];
diag = Map[Numerator[#]*Denominator[#]&,diag];
pfactors=Union[{2},First/@FactorInteger[Abs[Times@@diag]]];
Select[pfactors,Not[QpTernaryIsotropicQ[DiagonalMatrix[diag],#]]&]
]
computeGKint[mmm_List,prime_,printtraceQ_:False]:=Block[{m,Qmat,out,tttlist},
{m[1],m[2],m[3]}=mmm;
If[prime>4 m[1]m[2]m[3],Return[0]];
Qmat={{m[1],t[3]/2,t[2]/2},{t[3]/2,m[2],t[1]/2},{t[2]/2,t[1]/2,m[3]}};
tttlist =L2list[mmm,prime];
If[printtraceQ,Print[{prime,tttlist}]];
Total[Table[GKcontrib[(Qmat/.(Inner[Rule,Array[t,3],tt[[1]],List])),prime],{tt,tttlist}]]/2
]
computeGKint[mmm_List,printtraceQ_:False]:=Block[{m,out={}},
Do[
If[printtraceQ,Print[prime]];
AppendTo[out,{prime,computeGKint[mmm,prime,printtraceQ]}]
,{prime,Prime[Range[PrimePi[4 Times@@mmm]]]}
];
Select[out,#[[2]]!=0&]
]
(* lattice points inside an ellipse *)
Lptsbdy[a_,b_,c_,T_] :=Lptsbdy[a,b,c,T]= Block[{g,x,y,xmax,ymax,aa,bb,cc,irr,disc,x0min,x0max,nobdryQ,out},
{aa,bb,cc}=If[a>c,{c,b,a},{a,b,c}];
g[x_,y_]:=aa x^2+bb x y+cc y^2-T;
disc=-(bb^2-4 aa cc);
xmax=Floor[(2 Sqrt[cc] Sqrt[T])/Sqrt[disc]];
ymax=Floor[(2 Sqrt[aa] Sqrt[T])/Sqrt[disc]];
nobdryQ=True;
out = {};
(* fix y and get the range of x; *)
Do[irr=Sqrt[4 aa T+bb^2 y^2-4 aa cc y^2];x0min=(-bb y-irr)/(2 aa);x0max=(-bb y+irr)/(2 aa);nobdryQ=nobdryQ&&Not[IntegerQ[x0min]]&&Not[IntegerQ[x0max]];AppendTo[out,{{Ceiling[x0min],Floor[x0max]},y}],
{y,0,ymax}];
{nobdryQ,out}
]
Lpts[a_,b_,c_,T_]:=Block[{bdyset,out},
bdyset = Lptsbdy[a,b,c,T][[2]];
Do[If[xxy[[2]]!=0,AppendTo[bdyset,{{-xxy[[1]][[2]],-xxy[[1]][[1]]},-xxy[[2]]}]],{xxy,bdyset}];
out = Flatten[Table[{x,xxy[[2]]},{xxy,bdyset},{x,xxy[[1]][[1]],xxy[[1]][[2]]}],1];
out = If[a>c,Reverse/@out,out];
out
]
L1list[mmm_List]:= checkGKtripleQ[mmm][[2]]
L2list[mmm_List]:=L2list[mmm]=Block[{m,t,Qmat,matlist},
{m[1],m[2],m[3]}=mmm;
Qmat={{m[1],t[3]/2,t[2]/2},{t[3]/2,m[2],t[1]/2},{t[2]/2,t[1]/2,m[3]}};
matlist = Map[{#,QpTernaryAnisotropicPrimes[Qmat/.(Inner[Rule,Array[t,3],#,List])]}&,L1list[mmm]];
Select[matlist,Length[#[[2]]]==1&]
]
L2list[mmm_List,prime_]:=Select[L2list[mmm],#[[2]]=={prime}&]
checkGKtripleQ[mmm_List]:=checkGKtripleQ[mmm]=Block[{maxt3,m,t,nobdryQ,tempL1,val,target,lpts,squareintQ},
{m[1],m[2],m[3]}=mmm;
maxt3=Floor[2Sqrt[m[1]*m[2]]];
(* note that 4m[i]m[j] with i\[NotEqual]j should not be a perfect square *);
squareintQ[nn_]:=And@@(EvenQ/@Map[Last,FactorInteger[nn]]);
If[(squareintQ[m[1]m[2]])||(squareintQ[m[2]m[3]])||squareintQ[m[2]m[3]],val={False,{}};Goto["finish"]];
nobdryQ=True;tempL1={};
Do[
target=(4m[1]m[2]m[3]-m[3]t[3]^2);
(* lpts should not contain any boundary points; then Qmat is positive semi-definite *)
nobdryQ = Lptsbdy[m[1],-t[3],m[2],target][[1]]; 
(* nobdryQ=And@@(m[1]#[[1]]^2-t[3]#[[1]]#[[2]]+m[2]#[[2]]^2<target&/@lpts); *)
If[nobdryQ,
(* use the fact that Lpts[m[1],-t[3],m[2],target] and Lpts[m[1], t[3],m[2],target] are almost the same (not the same!!) *)
lpts =Lpts[m[1],-t[3],m[2],target];
tempL1=If[t[3]!=0,Join[tempL1,Append[#,t[3]]&/@lpts,{#[[1]],-#[[2]],-t[3]}&/@lpts],Join[tempL1,Append[#,t[3]]&/@lpts]],
val={False,{}};Goto["finish"]];
,{t[3],0,maxt3}];
val={True,tempL1};
Label["finish"];
val
]


End[];


EndPackage[]
