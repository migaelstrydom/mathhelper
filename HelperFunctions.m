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
(*OrthogTerm[term_,sumvar_]:=Module[{t},
t=Simplify[Evaluate[term]]/.b_ Exp[a_]->{a,b};
Simplify[term/.Solve[t[[1]]==0,sumvar][[1]]]
];
OrthogIntegrate[equation_,sumvar_]:=Module[{eq},
eq=Expand[equation];
If[MatchQ[eq,a_+b_],
Apply[Plus,OrthogTerm[#,sumvar]&/@Table[eq[[nnuniquenn]],{nnuniquenn,Length[eq]}]],
OrthogTerm[eq,sumvar]
]
];*)
(* Still need to test this version thoroughly. *)
OrthogTerm[term_,var_,sumvar_]:=Module[{t},
t=Simplify[Evaluate[term]]/.\[FormalB]_ Exp[\[FormalA]_]->{\[FormalA],\[FormalB]};
Simplify[term/.Solve[FindTermsWith[t[[1]],var]==0,sumvar][[1]]]
];
OrthogIntegrate[equation_,var_,sumvar_]:=Module[{eq},
eq=Expand[equation];
If[MatchQ[eq,a_+b_],
Apply[Plus,OrthogTerm[#,var,sumvar]&/@Table[eq[[\[FormalN]]],{\[FormalN],Length[eq]}]],
OrthogTerm[eq,var,sumvar]
]
];

(* Finds patt in expr and returns its precise form in expr. Returns a list of all occurrences. *)
FindPattern[expr_,patt_]:=Part[expr,##]&@@#&/@Position[expr,patt];

FindTermsWith[equation_, field_]:=Module[{eq},
	eq=Expand[equation];
	If[MatchQ[eq,a_+b_],
		Collect[
			Apply[Plus,eq[[#]]&/@Union[(Position[eq,field][[#,1]]&/@Range[Length[Position[eq,field]]])]],
			TandD[field],
			Simplify
		]
	,
		If[Position[eq,field]=={}, 0, eq]
	]
];
(* For collect statements: return a list containing patterns matching the function and its derivatives. *)
TandD[func_]:={func[__],Derivative[__][func][__]};

(* Takes a term and counts how many powers of a given set of fields it contains. eg CountFields[Ex[x,y,u]^3 bEx[x,y,u],{Ex,bEx}] gives 4.*)
CountFields[term_,fields_]:=Module[{aoeu,a,n},
Length[Flatten[ReleaseHold[(#/.{a_^n_->Hold[Table[a,{aoeu,n}]]})]&/@(term[[#]]&/@Union[Flatten[(#[[1]]&/@Position[term,#]&/@fields)]])]]
];

(* Separates a term into factors that depend on dep and those that do not.*)
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

Linspace[a_, b_, num_Integer] := Array[# &, num, {a, b}];

(*
	Counts the number of derivatives with respect to a specific variable.
*)
CountDerivatives[Derivative[derivatives__][_][parameters__],variable_]:=(
	List[derivatives][[Position[List[parameters],variable][[1,1]]]]
);

(*
    Takes an equation an extracts the name of the field with the highest derivative. If there are no such fields, it 
    returns {}. If there are many such fields, it takes the last one according to Mathematica's internal sort.
*)
HighestDerivativeField[eq_]:=Block[{a},
  If[Position[eq,Derivative[__][__][__]]=!={},
    Last[Sort[Extract[eq,Position[eq,Derivative[__][__][__]]]]]/.Derivative[__][a_][__]->a,
    {}
  ]
];

(* 
   Takes an equation and a field name. Renormalizes the equation so that the highest derivative term in the field has 
   unit coefficient. Works well with HighestDerivativeField.
*)
NormalizeEquation[eq_,field_]:=Module[{fieldWithDeriv},
  fieldWithDeriv=Last[Flatten[Extract[eq,#]&/@(Position[eq,#]&/@TandD[field])]];
  Collect[eq /Coefficient[eq,fieldWithDeriv],TandD[field],Simplify]
];

(* Same as above, but with a default value for field. *)
NormalizeEquation[eq_]:=Module[{HDF},
  HDF=HighestDerivativeField[eq];
  If[HDF=!={},
  NormalizeEquation[eq,HDF],
  eq]
];

(*  
ChangeVariables[f[x]f''[x],x,y,1/y,1/x,{f}]
gives
f[y] (2 y^3 (f^\[Prime])[y]+y^4 (f^\[Prime]\[Prime])[y])

validFunctions is a list of functions for which the argument is directly changed from old to new, not to oldequals.
*)
ChangeVariables[eq_, old_Symbol, new_Symbol, 
	oldEquals_, newEquals_, validFunctions_List] := Block[{UnSym},
  UnSym = Unique[];
  eq /. {
	Func_[a___, old, b___] /; (MemberQ[validFunctions, Func]) :> Func[a, UnSym, b] ,
    Derivative[dp__][Func_][a___, old, b___] /; (MemberQ[validFunctions, Func]) :> 
		Apply[D[Func[a, newEquals, b], ##] &, 
			Thread[({#1, #2}&)[{a, old, b}, {dp}]]
		] 
  } /. old->oldEquals /. UnSym->new
]

(* Give this function a series (with head SeriesData) and it will return the leading coefficient. If the SeriesData is empty
  (which means it is zero up to higher order corrections), it returns 0.
 *)
LeadingCoefficient[s_]:=If[Head[s]===SeriesData,
If[Level[s,1][[3]]==={},0,Level[s,1][[3,1]]],
s];

(* Give this function the output of Solve. *)
repSolutionFunction={HoldPattern[\[FormalA]_[pa__]->\[FormalB]_]->\[FormalA]->Function[{pa},\[FormalB]]};

(* Takes a term of the form (a x^3+b x^2+c x+d)Exp[e x^2+f x+g], finds the coefficients a-g, and integrates, assuming e < 0 *)
IntegrateExponentTerm[term_]:=Module[{coeffs,a,b,c,d,e,f,g,CcUniqueNameHopefully,eeUniqueNameHopefully},
coeffs=term/.{CcUniqueNameHopefully_  Exp[eeUniqueNameHopefully_]->{CcUniqueNameHopefully,eeUniqueNameHopefully}};
If[coeffs==term,
Print["Matching error in IntegrateExponentTerm."];
Return[];
];
{d,c,b,a}=PadRight[CoefficientList[coeffs[[1]],x],4];
{g,f,e}=PadRight[CoefficientList[coeffs[[2]],x],3];
(E^(-(f^2/(4 e))+g) (-8 d e^3-6 a e f+4 c e^2 f+a f^3-2 b e (-2 e+f^2)) Sqrt[\[Pi]])/(8 (-e)^(7/2))
];

IntegrateExponentEquation[equation_]:=Module[{eq,nn,a,b},
eq=Expand[equation];
If[MatchQ[eq,a_+b_],
Apply[Plus,IntegrateExponentTerm[#]&/@(Table[eq[[\[FormalN]]],{\[FormalN],Length[eq]}])],
IntegrateExponentTerm[eq]
]
];

(* 
  Works like series, except expands in (x0-x) instead of (x-x0). This gets rid of the annoying i\pi in the following:
  Series[u ^2Log[1-u^2],{u,1,0}]
  SeriesFromBelow[u ^2Log[1-u^2],{u,1,0}]
  Series[(u-1)^m u ^2Log[1-u^2],{u,1,0}]
  SeriesFromBelow[(u-1)^m u ^2Log[1-u^2],{u,1,0}]
*)
SeriesFromBelow[f_,{x_,x0_,n_}]:=Module[{y,tmp},
  Series[f/.x->x0-y,{y,0,n}]
    /.{HoldPattern[a_ SeriesData[y,0,L_,orders__]]:>(a/.y->x0-x)SeriesData[x,x0,L/.y->x0-x,orders]}
    /.{HoldPattern[SeriesData[y,0,L_,orders__]]:>SeriesData[x,x0,L/.y->x0-x,orders]}
];

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

GetRepPauliIdentities[\[Sigma]s_]:={\[Sigma]s[i_]**\[Sigma]s[j_]:>KroneckerDelta[i,j]+I Sum[Signature[{i,j,k}]\[Sigma]s[k],{k,3}]};

ToPythonString[expr_]:=Switch[expr,
Times[a_,Power[b_,-1]],expr/.{Times[a_,Power[b_,-1]]:>"("<>ToPythonString[a]<>"/"<>ToPythonString[b]<>")"},
Times[a_,b_],expr/.{Times[a_,b_]:>"("<>ToPythonString[a]<>"*"<>ToPythonString[b]<>")"},
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

ToMatlabString[expr_]:=Switch[expr,
Times[a_,Power[b_,-1]],expr/.{Times[a_,Power[b_,-1]]:>"("<>ToMatlabString[a]<>"./"<>ToMatlabString[b]<>")"},
Times[a_,b_],expr/.{Times[a_,b_]:>"("<>ToMatlabString[a]<>".*"<>ToMatlabString[b]<>")"},
Plus[a_,Times[-1,b_]],expr/.{Plus[a_,Times[-1,b_]]:>"("<>ToMatlabString[a]<>"-"<>ToMatlabString[b]<>")"},
Plus[a_,b_],expr/.{Plus[a_,b_]:>"("<>ToMatlabString[a]<>"+"<>ToMatlabString[b]<>")"},
Power[a_,b_],expr/.{Power[a_,b_]:>ToMatlabString[a]<>".^"<>ToMatlabString[b]},
Rational[a_?NumberQ,b_?NumberQ],expr/.{Rational[a_,b_]:>"("<>ToMatlabString[a]<>"/"<>ToMatlabString[b]<>")"},
s_[a__],expr/.{s_[a__]:>ToString[s]},
_,ToString[expr]
];

ToMatlab[expr_]:=Module[{derex},
derex=Evaluate[
expr//.{Derivative[da___,d_,db___][s_][aa___,a_,ab___]/;(Length[{da}]==Length[{aa}] &&Length[{db}]==Length[{ab}]&&d>1):>Derivative[da,0,db][Symbol["d"<>ToString[d]<>ToString[s]<>"d"<>ToString[a]<>ToString[d]]][aa,a,ab]}//.{Derivative[da___,d_,db___][s_][aa___,a_,ab___]/;(Length[{da}]==Length[{aa}] &&Length[{db}]==Length[{ab}]&&d==1):>Derivative[da,0,db][Symbol["d"<>ToString[s]<>"d"<>ToString[a]]][aa,a,ab]}
];
ToMatlabString[derex]
];
