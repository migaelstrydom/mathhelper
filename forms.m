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

(* Must be defined: xmu, dim, met *)
Clear[xmu,dim,met,metinv,ch];

Clear[IsCoordinate]
IsCoordinate[a_]:=Position[xmu,a]!={};

Clear[IsForm,IsOneForm,Wedge,d];

IsOneForm[d[a_]]:=IsCoordinate[a];
IsOneForm[c_ d[a_]]:=IsCoordinate[a];
SetAttributes[IsForm,Listable];
IsForm[d[a_]]:=IsCoordinate[a];
IsForm[c_ d[a_]]:=IsCoordinate[a];
IsForm[Wedge[a__]]:=IsForm[{a}]===ConstantArray[True,Length[{a}]];
IsForm[c_ Wedge[a__]]:=IsForm[Wedge[a]];
IsForm[a_+b_]:=IsForm[a]&&IsForm[b];
IsForm[_]:=False;

(*SetAttributes[Wedge,Flat];*)
Wedge[a_]:=a;
Wedge[fi___,HoldPattern[Wedge[w__]],la___]:=Wedge[fi,w,la];
Wedge[fi___,HoldPattern[a_ Wedge[w__]],la___]:=Wedge[fi,a ,w,la];
Wedge[fi___,a_,la___]/;(!IsForm[a]&&Length[{fi,la}]>1):=a Wedge[fi,la];
Wedge[fi___,a_ d[f_],la___]:=a Wedge[fi,d[f],la];
Wedge[fi___,a_+b_,la___]:=Wedge[fi,a,la]+Wedge[fi,b,la];
Wedge[fi___,d[a_],d[a_],la___]:=0;
Wedge[a__]/;(Position[{a},Wedge]=={}&&!OrderedQ[{a}]):=(Signature[{a}]Wedge@@Sort[{a}]);

SetAttributes[d,Listable]
d[a_+b_]:=d[a]+d[b];
d[d[co_]]=0;
d[_?NumberQ]=0;
d[a_ d[co_]]:=Sum[D[a,xmu[[ssi]]] d[xmu[[ssi]]]\[Wedge]d[co],{ssi,1,dim}];
d[HoldPattern[Wedge[b__]]]:=0;
d[a_ HoldPattern[Wedge[b__]]]:=Sum[D[a,xmu[[ssi]]]Wedge[d[xmu[[ssi]]],b],{ssi,1,dim}];
(*d[a_ HoldPattern[Wedge[b__]]]:=Module[{WedgeSymbol,xmuSymbol,chSymbol,\[Nu]Sum,\[Alpha]Sum},
Sum[D[a,xmu[[\[Nu]Sum]]]Wedge[d[xmu[[\[Nu]Sum]]],b],{\[Nu]Sum,1,dim}]-
Sum[
Plus@@((a chSymbol[coordPosition[{b}[[#]]/.d[s_]:>s],\[Alpha]Sum,\[Nu]Sum](WedgeSymbol[d[xmuSymbol[\[Alpha]Sum]],##]&@@(ReplacePart[{b},#->d[xmuSymbol[\[Nu]Sum]]]))&/@Range[Length[{b}]])),
{\[Alpha]Sum,1,dim},{\[Nu]Sum,1,dim}
]/.{xmuSymbol[\[Mu]_]:>xmu[[\[Mu]]]}/.{WedgeSymbol[w__]:>Wedge[w]}/.{chSymbol[chs__]:>ch[[chs]]}
];*)

Clear[coordPosition,ComponentsSingleTerm,Components];
coordPosition[a_]:=coordPosition[a]=Position[xmu,a][[1,1]];

FormCoefficientBasis[Qf_]:=Module[{dummy},
If[Position[Qf,Wedge]!={},
	dummy Qf/.{a_ HoldPattern[Wedge[b__]]->{a/dummy,{b}}},
	If[MatchQ[dummy Qf,_ d[_]],
		dummy Qf/.{a_ d[b_]->{a/dummy,{d[b]}}},
		{Qf,{}}
	]
  ]
];

ComponentsSingleTerm[Qf_]:=Module[{rank,coeff,form},
{coeff,form}=FormCoefficientBasis[Qf];
rank=Length[form];
form=ReleaseHold[(Hold[coordPosition[#]]/.{HoldPattern[d[co_]]->co})&/@form];
coeff=coeff*Signature[form];
form=Sort[form];

Array[If[Sort[{##}]==form,Signature[{##}]coeff,0]&,ConstantArray[dim,rank]]
];
Components[form_]:=Module[{Qf},
Qf=Expand[form];
If[MatchQ[Qf,a_+b_],
ComponentsSingleTerm/@Qf,
ComponentsSingleTerm[Qf]
]
];

HodgeSingleTerm[Qf_]:=Module[{rank,coeff,form,syms\[Mu],syms\[Nu],
gSymbol,EpsilonSymbol,WedgeSymbol,xmuSymbol},
{coeff,form}=FormCoefficientBasis[Qf];
rank=Length[form];
form=ReleaseHold[(Hold[coordPosition[#]]/.{HoldPattern[d[co_]]->co})&/@form];
syms\[Mu]=(Symbol["\[Mu]"<>ToString[#]]&/@Range[rank]);
syms\[Nu]=(Symbol["\[Nu]"<>ToString[#]]&/@Range[dim-rank]);

Sum[(Sum[(Evaluate[
(1/(Factorial[dim-rank]))coeff*
(Times@@(gSymbol[form[[#]],syms\[Mu][[#]]]&/@Range[rank]))*
(EpsilonSymbol[{(##&@@syms\[Mu]),(##&@@syms\[Nu])}])*
(WedgeSymbol@@(d[xmuSymbol[#]]&/@syms\[Nu]))
]),##]&@@({#,1,dim}&/@syms\[Mu])),
##]&@@({#,1,dim}&/@syms\[Nu])/.{
EpsilonSymbol->Signature,xmuSymbol[a_]:>xmu[[a]],WedgeSymbol->Wedge,gSymbol[a_,b_]:>metinv[[a,b]]
}
];
Hodge[form_]:=Module[{Qf},
Qf=Expand[form];
Sqrt[-Det[met]]If[MatchQ[Qf,a_+b_],
HodgeSingleTerm[#]&/@Qf,
HodgeSingleTerm[Qf]
]
];
