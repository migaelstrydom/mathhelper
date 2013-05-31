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

(* Christoffel Symbols *)
Christoffel[met_,var_] := Module[{Dmet,metinv},
    Dmet= Outer[D,met,var] ;
    metinv= Inverse[met]//Simplify;
    1/2( Transpose[metinv.Dmet,{1,3,2}]+
    Transpose[metinv.Dmet,{1,2,3}]-
    metinv.Transpose[Dmet,{3,2,1}] )
];

(* Just the non-zero components of a tensor *)
NonZeroComponents[sym_,comp_,coord_]:=Module[{NZIndices,toCoord},
    NZIndices=Select[Flatten[Array[{##}&,Dimensions[comp]],Length[Dimensions[comp]]-1],(Part[comp,##]&)@@#=!=0&];
    (((sym@@Thread[toCoord[#]])->(comp[[##]]&)@@#)&/@NZIndices)/.toCoord[a_]:>coord[[a]]
]

(* Indices: (Up, Down, Down, Down) *)
RiemannTensor[ch_,coord_]:=Module[{Dch,ch2},
    Dch=Outer[D,ch,coord];
    ch2=ch.ch;
    Transpose[Dch,{1,4,2,3}]-Transpose[Dch,{1,3,2,4}]+
    Transpose[ch2,{1,3,4,2}]-Transpose[ch2,{1,4,3,2}]
];

RicciTensor[RiemannT_]:=(
    Tr[Transpose[RiemannT,{1,3,2,4}],Plus,2]
);

RicciScalar[RicciT_,metinv_]:=(
    Tr[metinv.RicciT]
);

(* All indices down. Coordinate index comes first. *)
Vielbein[ea_,eta_,ch_,var_]:=
    Transpose[(eta.ea.Outer[D,Inverse[ea],var]),{2,3,1}]+
    Transpose[(eta.ea.ch.Inverse[ea]),{2,1,3}];
