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

ChebyshevGrid[xSmall_, xLarge_, n_Integer/;n>1] := 
	xSmall+1/2 (xLarge-xSmall) (1-Cos[\[Pi] Range[0,n-1]/(n-1)]);

CollocationPointsFactory[collPoints_, start_, end_, numberOfPoints_, label_] := (

	Clear[collPoints];

	collPoints[number] = numberOfPoints;
	collPoints[label] = N[ChebyshevGrid[start, end, collPoints[number]]];
	collPoints[zeroes] = ConstantArray[0., collPoints[number]];
	collPoints[ones] = ConstantArray[1., collPoints[number]];

	collPoints[interpolation][ps_?ListQ] :=
		Interpolation[Thread[({#1,#2}&)[collPoints[label],ps]],InterpolationOrder->collPoints[number]-1];

	collPoints[diff][y_?ListQ,n_Integer/;n>0] :=
		NDSolve`FiniteDifferenceDerivative[n,collPoints[label],y,
			PeriodicInterpolation->False,"DifferenceOrder"->"Pseudospectral"];
	collPoints[diff][y_?ListQ] := collPoints[diff][y,1];

	collPoints[diffmatrix][n_Integer/;n>0] :=
		NDSolve`FiniteDifferenceDerivative[{n},{collPoints[label]},
			"DifferenceOrder"->"Pseudospectral",PeriodicInterpolation->{False}]@"DifferentiationMatrix";

	collPoints[integrate][ps_?ListQ] := (
		Head[Integrate[
				Interpolation[Thread[({#1,#2}&)[collPoints[label],ps]],
					InterpolationOrder->collPoints[number]-1][z],
			z]
		]/@collPoints[label]
	);
	collPoints[plot][y_?ListQ,plotOptions___] := 
		Show[
			{ListLinePlot[Thread[({#1,#2}&)[collPoints[label],y]],InterpolationOrder->collPoints[number]-1, plotOptions],
				ListPlot[Thread[({#1,#2}&)[collPoints[label],y]],PlotStyle->PointSize[0.02]]},
			plotOptions
		];
	collPoints[evaluate][field_,x_List] :=
		With[{cp=collPoints[label],numPoints=collPoints[number]},
			Interpolation[{cp[[#]],collPoints[field][[#]]}&/@Range[numPoints],InterpolationOrder->numPoints-1]/@x
		];

	collPoints[substitute][fieldList_] = {
		Derivative[dz__][field_][p__]/;MemberQ[fieldList,field]:>
			collPoints[diff][collPoints[field],CountDerivatives[Derivative[dz][field][p],label]],
		field_[p__]/;MemberQ[fieldList,field]:>collPoints[field],
		label->collPoints[label]
	};

	collPoints[substituteAnalytic][fieldList_List] := {
		Derivative[dz__][field_][p__]/;MemberQ[fieldList, field]:>
			collPoints[diffmatrix][CountDerivatives[Derivative[dz][field][p],label]].Table[field[\[FormalI]],{\[FormalI],collPoints[number]}],
		field_[p__]/;MemberQ[fieldList,field]:>Table[field[\[FormalI]],{\[FormalI], collPoints[number]}],
		label->collPoints[label]
	};

	collPoints[fieldTable][field_] := Table[field[\[FormalI]], {\[FormalI], collPoints[number]}];

	(*
	ResizeCollGrid[oldPoints_?ListQ,newSize_?IntegerQ]:=Module[{oldCollPoints,newCollPoints,interpolatingFunction},
	oldCollPoints=N[ChebyshevGrid[collPoints[\[Epsilon]],1-collPoints[\[Epsilon]],Length[oldPoints]]];
	newCollPoints=N[ChebyshevGrid[collPoints[\[Epsilon]],1-collPoints[\[Epsilon]],newSize]];
	interpolatingFunction=Interpolation[({oldCollPoints[[#]],oldPoints[[#]]}&/@Range[Length[oldCollPoints]]),InterpolationOrder\[Rule]Length[oldCollPoints]-1];
	interpolatingFunction/@newCollPoints
	];
	*)
);

EvenlySpacedPointsFactory[esPoints_, start_, end_, numberOfPoints_, label_] := (
	Clear[esPoints];
	esPoints[number] = numberOfPoints;
	esPoints[label] = Linspace[start, end, esPoints[number]];
	esPoints[zeroes] = ConstantArray[0.,esPoints[number]];
	esPoints[ones] = ConstantArray[1.,esPoints[number]];
	esPoints[spacing] = esPoints[label][[2]]-esPoints[label][[1]];

	esPoints[interpolation][ps_?ListQ] := Interpolation[Thread[({#1,#2}&)[esPoints[label],ps]]];

	esPoints[plot][ps_?ListQ,plotOptions___] := ListLinePlot[Thread[({#1,#2}&)[esPoints[label],ps]],AxesOrigin->{0,0},plotOptions];
	esPoints[plot][field_?(MemberQ[tfields,#]&)] := esPoints[plot][esPoints[field]];

	(*esPoints[diff][ps_?ListQ,n_Integer/;n>0]:=(Head[D[Interpolation[Thread[({#1,#2}&)[esPoints[label],ps]],InterpolationOrder\[Rule]esPoints[number]-1][z],z]]/@esPoints[label]);*)
	esPoints[diff][ps_?ListQ,n_Integer/;n>0]:=NDSolve`FiniteDifferenceDerivative[n,esPoints[label],ps,PeriodicInterpolation->False,"DifferenceOrder"->8,PeriodicInterpolation->{False}];
	esPoints[diff][field_?(MemberQ[tfields,#]&),n_Integer/;n>0]:=esPoints[diff][esPoints[field],n];
	esPoints[diff][ps_]:=esPoints[diff][ps,1]
	esPoints[diffmatrix][n_Integer/;n>0]:=
		NDSolve`FiniteDifferenceDerivative[{n},{esPoints[label]},"DifferenceOrder"->8,PeriodicInterpolation->{False}]@"DifferentiationMatrix";

	esPoints[integrate][ps_?ListQ]:=(Head[Integrate[Interpolation[Thread[({#1,#2}&)[esPoints[label],ps]]][z],z]]/@esPoints[label]);

	esPoints[substitute][fieldList_] = {
		Derivative[dz__][field_][p__]/;MemberQ[fieldList,field]:>esPoints[diff][esPoints[field],CountDerivatives[Derivative[dz][field][p],label]],
		field_[p__]/;MemberQ[fieldList,field]:>esPoints[field],
		label->esPoints[label]
	};

	esPoints[substituteAnalytic][fieldList_List] := {
		Derivative[dz__][field_][p__]/;MemberQ[fieldList,field]:>esPoints[diffmatrix][CountDerivatives[Derivative[dz][field][p],label]].Table[field[\[FormalI]],{\[FormalI],esPoints[number]}],
		field_[p__]/;MemberQ[fieldList,field]:>Table[field[\[FormalI]],{\[FormalI],esPoints[number]}],
		label->esPoints[label]
	};

	esPoints[fieldTable][field_]:=Table[field[\[FormalI]],{\[FormalI],esPoints[number]}];
);

CollocationPoints2DFactory[collPoints2D_, zPoints_List, vPoints_List, zLabel_, vLabel_] := (

	Clear[collPoints2D];

	collPoints2D[zLabel] = zPoints;
	collPoints2D[vLabel] = vPoints;

	collPoints2D[number][zLabel]=Length[collPoints2D[zLabel]];
	collPoints2D[number][vLabel]=Length[collPoints2D[vLabel]];

	collPoints2D[diffMatrix][dz_,dy_] := collPoints2D[diffMatrix][dz,dy] =
		Normal[
			NDSolve`FiniteDifferenceDerivative[{dz,dy},{collPoints2D[zLabel],collPoints2D[vLabel]},PeriodicInterpolation->False,"DifferenceOrder"->"Pseudospectral"]["DifferentiationMatrix"]
		];
	collPoints2D[diff][dz_,dy_][fieldPoints_] :=
		NDSolve`FiniteDifferenceDerivative[
			{dz,dy},{collPoints2D[zLabel],collPoints2D[vLabel]},
			PeriodicInterpolation->False,"DifferenceOrder"->"Pseudospectral"][fieldPoints];

	collPoints2D[analytic][field_]:=Outer[Function[{i,j},field[i,j]],Range[Length[collPoints2D[zLabel]]],Range[Length[collPoints2D[vLabel]]]];

	collPoints2D[plot][data_,PlotOptions___] := 
		ListPlot3D[
			Flatten[Table[{collPoints2D[zLabel][[i]],collPoints2D[vLabel][[j]],data[[i,j]]},
				{i,collPoints2D[number][zLabel]},{j,collPoints2D[number][vLabel]}],
			1],
		PlotOptions];

	collPoints2D[substituteAnalytic][fields_]:=
		Join[
			Map[
				(Derivative[dz_,dv_][#][z,v]:>Partition[collPoints2D[diffMatrix][dz,dv].Flatten[collPoints2D[analytic][#]],collPoints2D[number][vLabel]])&,
				fields
			],
			Map[
				#[z,v]->collPoints2D[analytic][#]&,
				fields
			],
			{zLabel->collPoints2D[zLabel]}
		];

);

EvenlySpacedPoints2DFactory[esPoints2D_, zPoints_List, vPoints_List, zLabel_, vLabel_] := (

	Clear[esPoints2D];

	esPoints2D[zLabel] = zPoints;
	esPoints2D[vLabel] = vPoints;

	esPoints2D[number][zLabel] = Length[esPoints2D[zLabel]];
	esPoints2D[number][vLabel] = Length[esPoints2D[vLabel]];

	esPoints2D[diffMatrix][dz_,dy_] := esPoints2D[diffMatrix][dz,dy] =
		Normal[
			NDSolve`FiniteDifferenceDerivative[{dz,dy},{esPoints2D[zLabel],esPoints2D[vLabel]},PeriodicInterpolation->False,"DifferenceOrder"->8]["DifferentiationMatrix"]
		];
	esPoints2D[diff][dz_,dy_][fieldPoints_] :=
		NDSolve`FiniteDifferenceDerivative[
			{dz,dy},{esPoints2D[zLabel],esPoints2D[vLabel]},
			PeriodicInterpolation->False,"DifferenceOrder"->8][fieldPoints];

	esPoints2D[analytic][field_]:=Outer[Function[{i,j},field[i,j]],Range[Length[esPoints2D[zLabel]]],Range[Length[esPoints2D[vLabel]]]];

	esPoints2D[plot][data_,PlotOptions___] := 
		ListPlot3D[
			Flatten[Table[{esPoints2D[zLabel][[i]],esPoints2D[vLabel][[j]],data[[i,j]]},
				{i,esPoints2D[number][zLabel]},{j,esPoints2D[number][vLabel]}],
			1],
		PlotOptions];

	esPoints2D[substituteAnalytic][fields_]:=
		Join[
			Map[
				(Derivative[dz_,dv_][#][z,v]:>Partition[esPoints2D[diffMatrix][dz,dv].Flatten[esPoints2D[analytic][#]],esPoints2D[number][vLabel]])&,
				fields
			],
			Map[
				#[z,v]->esPoints2D[analytic][#]&,
				fields
			],
			{zLabel->esPoints2D[zLabel]}
		];

);
