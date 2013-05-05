(* ::Package:: *)

(*
Copyright 2013 Migael Strydom

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

FTransformFunctions[equation_,var_,toTransform_,periods_,parms_,vars_]:=Module[{eq,neweq,unsym,unsym2,i,j,k,v,termList,fPoses,repPowers},
eq=Expand[equation];
neweq=0;
unsym=Unique[];
unsym2=Unique[];
eq=eq+unsym2;
repPowers=Flatten[{#[y__]^(x_Integer?((#>1)&))->Hold[Table[#[y],{oaeu,x}]]&/@toTransform,
Derivative[d__][#][y__]^(x_Integer?((#>1)&))->Hold[Table[Derivative[d][#][y],{oaeu,x}]]&/@toTransform
}];
For[i=1,i<=Length[eq],i++,
v=1;
termList=Flatten[ReleaseHold[Level[unsym eq[[i]],1]/.repPowers]];
For[j=1,j<=Length[toTransform],j++,
fPoses=Position[termList,Evaluate[toTransform[[j]]]];
For[k=1,k<=Length[fPoses],k++,
termList[[fPoses[[k,1]]]]=termList[[fPoses[[k,1]]]]/.{
Evaluate[toTransform[[j]]]->Function[Evaluate[ToExpression["{"<>parms[[j]]<>"}"]],Evaluate[Exp[-I periods[[j]] vars[[v]] var] (ToExpression["t"<>ToString[toTransform[[j]]]<>"["<>parms[[j]]<>"]"] /.{var->vars[[v]]})]]
};
v++;
];
];
neweq=neweq+(Apply[Times,termList]/.{unsym->1});
(*Debug: *)
(*Print[eq[[i]],"       ",(Apply[Times,termList]/.{unsym->1})];*)
];
neweq-unsym2
];
OrthogTerm[term_,sumvar_]:=Module[{t},
t=Simplify[Evaluate[term]]/.b_ Exp[a_]->{a,b};
Simplify[term/.Solve[t[[1]]==0,sumvar][[1]]]
];
OrthogIntegrate[equation_,sumvar_]:=Module[{eq},
eq=Expand[equation];
If[MatchQ[eq,a_+b_],
Apply[Plus,OrthogTerm[#,sumvar]&/@Table[eq[[nnuniquenn]],{nnuniquenn,Length[eq]}]],
OrthogTerm[eq,sumvar]
]
];

FindTermsWith[equation_,field_]:=Module[{eq},
eq=Expand[equation];
Collect[
Apply[Plus,eq[[#]]&/@Union[(Position[eq,field][[#,1]]&/@Range[Length[Position[eq,field]]])]],
TandD[field],Simplify]
];
(* For collect statements: return a list containing patterns matching the function and its derivatives. *)
TandD[func_]:={func[__],Derivative[__][func][__]};

(* Takes a term and counts how many powers of a given set of fields it contains. eg CountFields[Ex[x,y,u]^3 bEx[x,y,u],{Ex,bEx}] gives 4.*)
CountFields[term_,fields_]:=Module[{aoeu,a,n},
Length[Flatten[ReleaseHold[(#/.{a_^n_->Hold[Table[a,{aoeu,n}]]})]&/@(term[[#]]&/@Union[Flatten[(#[[1]]&/@Position[term,#]&/@fields)]])]]
];

FactorOutTerm[term_,dep_]:=Module[{},
{Times@@(term[[#[[1]]]]&/@Position[term,dep]),
Times@@((term[[#]]&)/@Complement[Range[Length[term]],(#[[1]]&/@Position[term,dep])])}
];
FactorOut[expression_,dep_]:=Module[{e},
e=Expand[expression];
If[MatchQ[e,a_+b_],
FactorOutTerm[e[[#]],dep]&/@Range[Length[e]],
FactorOutTerm[e,dep]
]
];

(* Applies function func to an expression term by term. *)
TermByTerm[expr_,func_]:=(
If[MatchQ[expr,a_+b_],
  Plus@@(func/@Level[expr,1]),
  func[expr]
]
);

repSolutionFunction={HoldPattern[a_[pa__]->b_]->a->Function[{pa},b]};

FreeListQ[expr_,lst_]:=(
And@@(FreeQ[expr,#]&/@lst)
);

SetupNCM[nonCommutingSymbols_]:=(
SetAttributes[NonCommutativeMultiply,Listable];
ClearAttributes[NonCommutativeMultiply,Protected];
Clear[NonCommutativeMultiply];
0**_=0;
_**0=0;
a_**b_:=a b/;(FreeListQ[a,nonCommutingSymbols]||FreeListQ[b,nonCommutingSymbols]);
(c_ a_)**b_:=c a**b/;FreeListQ[c,nonCommutingSymbols];
a_**(c_ b_):=c a**b/;FreeListQ[c,nonCommutingSymbols];
(a_+b_)**c_:=a**c+b**c;
a_**(b_+c_):=a**b+a**c;
SetAttributes[NonCommutativeMultiply,Protected];
);

ClearNCM[]:=(
ClearAttributes[NonCommutativeMultiply,Protected];
ClearAttributes[NonCommutativeMultiply,Listable];
Clear[NonCommutativeMultiply];
SetAttributes[NonCommutativeMultiply,Protected];
);

GetRepNCM[nonCommutingSymbols_]:={
0**_->0,
_**0->0,
a_**b_:>a b/;(FreeListQ[a,nonCommutingSymbols]||FreeListQ[b,nonCommutingSymbols]),
(c_ a_)**b_:>c a**b/;FreeListQ[c,nonCommutingSymbols],
a_**(c_ b_):>c a**b/;FreeListQ[c,nonCommutingSymbols],
(a_+b_)**c_->a**c+b**c,
a_**(b_+c_)->a**b+a**c
};

GetRepCollectNCMRight[termFunc_]:={d1_ b_**a_+d2_ c_**a_:>(termFunc[d1 b+d2 c])**a,
b_**a_+d2_ c_**a_:>(termFunc[b+d2 c])**a,
d1_ b_**a_+c_**a_:>(termFunc[d1 b+c])**a,
 b_**a_+c_**a_:>(termFunc[b+c])**a
};

ToPythonString[expr_]:=Switch[expr,
\!\(\*
TagBox[
StyleBox[
RowBox[{"Times", "[", 
RowBox[{"a_", ",", 
RowBox[{"Power", "[", 
RowBox[{"b_", ",", 
RowBox[{"-", "1"}]}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\),expr/.{\!\(\*
TagBox[
StyleBox[
RowBox[{"Times", "[", 
RowBox[{"a_", ",", 
RowBox[{"Power", "[", 
RowBox[{"b_", ",", 
RowBox[{"-", "1"}]}], "]"}]}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\):>"("<>ToPythonString[a]<>"/"<>ToPythonString[b]<>")"},
Times[a_,b_],expr/.{\!\(\*
TagBox[
StyleBox[
RowBox[{"Times", "[", 
RowBox[{"a_", ",", "b_"}], "]"}],
ShowSpecialCharacters->False,
ShowStringCharacters->True,
NumberMarks->True],
FullForm]\):>"("<>ToPythonString[a]<>"*"<>ToPythonString[b]<>")"},
Plus[a_,Times[-1,b_]],expr/.{Plus[a_,Times[-1,b_]]:>"("<>ToPythonString[a]<>"-"<>ToPythonString[b]<>")"},
Plus[a_,b_],expr/.{Plus[a_,b_]:>"("<>ToPythonString[a]<>"+"<>ToPythonString[b]<>")"},
Power[a_,b_],expr/.{Power[a_,b_]:>ToPythonString[a]<>"**"<>ToPythonString[b]},
s_[a__],expr/.{s_[a__]:>ToString[s]},
_,ToString[expr]
];

ToPython[expr_]:=Module[{derex},
derex=Evaluate[
expr//.{Derivative[da___,d_,db___][s_][aa___,a_,ab___]/;(Length[{da}]==Length[{aa}] &&Length[{db}]==Length[{ab}]&&d>1):>Derivative[da,0,db][Symbol["d"<>ToString[d]<>ToString[s]<>"d"<>ToString[a]<>ToString[d]]][aa,a,ab]}//.{Derivative[da___,d_,db___][s_][aa___,a_,ab___]/;(Length[{da}]==Length[{aa}] &&Length[{db}]==Length[{ab}]&&d==1):>Derivative[da,0,db][Symbol["d"<>ToString[s]<>"d"<>ToString[a]]][aa,a,ab]}
];
ToPythonString[derex]
];
