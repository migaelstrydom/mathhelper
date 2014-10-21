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

(* The following symbols are defined in this package: *)
Clear[ChebyshevGrid,
	DifferentiateCollocationPoints,
	CollocationPointsFactory, 
	EvenlySpacedPointsFactory, 
	PointsPatchesFactory, 
	CollocationPoints2DFactory, 
	EvenlySpacedPoints2DFactory];

(* Produce a Chebyshev grid starting at xSmall, ending at xLarge and with n points. *)
ChebyshevGrid[xSmall_?NumberQ, xLarge_?NumberQ, n_Integer/;n>1] := 
	xSmall + 1/2 (xLarge-xSmall) (1 - Cos[\[Pi] Range[0, n-1] / (n-1)]);

(* Use NDSolve`FiniteDifferenceDerivative to differentiate "y" on the Chebyshev grid 
	"grid" with "n" points.
*)
DifferentiateCollocationPoints[grid_List, y_List, n_Integer /; n > 0] :=
	NDSolve`FiniteDifferenceDerivative[
		n, grid, y,
		PeriodicInterpolation->False, "DifferenceOrder"->"Pseudospectral"
	];
(* Define the zeroth order derivative of "y" on Chebyshev grid "grid". This is just the
   identity operator.
*)
DifferentiateCollocationPoints[grid_List, y_List, 0] := y;

(* Return the differentiation operator as a matrix, which can act on a vector "y" of
   points on a Chebyshev grid. *)
DiffMatrixCollocationPoints[grid_List, n_Integer /; n > 0] :=
	With[{id = IdentityMatrix[Length[grid]]},
		Transpose[Table[DifferentiateCollocationPoints[grid, id[[i]], n], {i, Length[grid]}]]
	];
	(* This official method has a bug. It returns the wrong differentiation matrix 
	   when Precision \[NotEqual] MachinePrecision. *)
	(*NDSolve`FiniteDifferenceDerivative[{n}, {grid},
		"DifferenceOrder"->"Pseudospectral",
		PeriodicInterpolation->{False}]["DifferentiationMatrix"];
	*)
(* Special case: returns the identity matrix for zeroth order derivatives. *)
DiffMatrixCollocationPoints[grid_List, 0] := IdentityMatrix[Length[grid]];

(* By default we initialise the points with MachinePrecision. *)
Options[CollocationPointsFactory] = {Precision -> MachinePrecision};

(* Create a structure containing Chebyshev points and functions that can operate on those points.

	collPoints: A symbol that will be populated with the structure's properties and methods.
	start: The smallest point in the Chebyshev grid.
	end: The biggest point in the Chebyshev grid.
	numberOfPoints: The number of points in the Chebyshev grid.
	label: A symbol specifying the coordinate name, such as "x".
	Options: 
		Precision: A precision setting given to Mathematica. The default value is 
			"MachinePrecision".

	The structure collPoints will be populated with the following properties and methods.
	Properties:
	collPoints[number]: The number of points on the Chebyshev grid.
	collPoints[precision]: The precision of the points.
	collPoints[label]: The list of Chebyshev points.
	collPoints[zeroes]: A list of zeroes with length collPoints[number].
	collPoints[ones]: A list of ones with length collPoints[number].
	Methods:
	collPoints[interpolation][ps_]: Treats ps as a list f(x_i) of function values of f at
		Chebyshev points x_i. Returns an interpolating function f made out of those points.
	collPoints[diff][y_, n_]: Treats y as a function y(x_i), with x_i the Chebyshev points. Returns
		the points of the nth derivative d^(n) y / dx.
	collPoints[diffMatrix][n_]: Returns the nth-order differentiation matrix for the Chebyshev 
		points.	
	collPoints[integrate][y_]: Treats y as a function y(x_i), with x_i the Chebyshev points. 
		Returns the points of the integral \int y dx. WARNING: This does not use pseudospectral 
		methods.
	collPoints[plot][y_, plotOptions_]: Plots the points y(x_i). PlotOptions:
		ShowPoints: True/False, whether to plot the individual points.
		ShowLine: True/False, whether to draw an interpolating line on the plot.
	collPoints[evaluate][ps_, x_]: Turns the points list ps into an interpolating function and
		evaluates it at the points in the list x.
	collPoints[substitute][fieldList, pointsStructure]: Returns a list of replacement rules that
		can be used to substitute into an expression involving the fields in fieldList and their
		derivatives.
*)

CollocationPointsFactory[collPoints_Symbol, start_?NumberQ, end_?NumberQ, 
		numberOfPoints_Integer, label_Symbol, OptionsPattern[]] := (

	Clear[collPoints];

	collPoints[number] = numberOfPoints;
	collPoints[precision] = OptionValue[Precision];
	collPoints[label] = ChebyshevGrid[SetPrecision[start, OptionValue[Precision]], 
									 SetPrecision[end, OptionValue[Precision]],
									 collPoints[number]];
	collPoints[zeroes] = SetPrecision[ConstantArray[0, collPoints[number]], OptionValue[Precision]];
	collPoints[ones] = SetPrecision[ConstantArray[1, collPoints[number]], OptionValue[Precision]];

	collPoints[interpolation][ps_?ListQ] :=
		Interpolation[Thread[({#1,#2}&)[collPoints[label], ps]], 
			InterpolationOrder -> collPoints[number]-1
		];

	collPoints[diff][y_List, n_Integer /; n >= 0] := 
		DifferentiateCollocationPoints[collPoints[label], y, n];

	collPoints[diff][y_List] := collPoints[diff][y, 1];

	collPoints[diffMatrix][n_Integer /; n >= 0] := collPoints[diffMatrix][n] = 
		DiffMatrixCollocationPoints[collPoints[label], n];

	collPoints[integrate][ps_?ListQ] := (
		Head[Integrate[
				Interpolation[Thread[({#1,#2}&)[collPoints[label],ps]],
					InterpolationOrder->collPoints[number]-1][z],
			z]
		]/@collPoints[label]
	);
	collPoints[plot][y_?ListQ, plotOptions___] := Module[{pointPairs, showList, sanitisedPlotOptions},
		pointPairs = Thread[({#1,#2}&)[collPoints[label], y]];
		sanitisedPlotOptions = Apply[Sequence,
			DeleteCases[List[plotOptions], (ShowPoints -> _) | (ShowLine -> _)]
		];
		showList = {};

		If[(ShowPoints /. List[plotOptions]) =!= False, 
			AppendTo[showList, ListPlot[pointPairs, PlotStyle -> PointSize[0.02],
				sanitisedPlotOptions
			]]
		];
		If[(ShowLine /. List[plotOptions]) =!= False, 
			AppendTo[showList, 
				ListLinePlot[pointPairs, InterpolationOrder -> collPoints[number] - 1, 
					sanitisedPlotOptions
				]
			]
		];
		
		Show[showList, sanitisedPlotOptions]
	];

	collPoints[evaluate][ps_List,x_List] :=
		With[{cp=collPoints[label],numPoints=collPoints[number]},
			Interpolation[{cp[[#]],ps[[#]]}&/@Range[numPoints],InterpolationOrder->numPoints-1]/@x
		];

	collPoints[evaluate][field_Symbol,x_List] :=
		With[{cp=collPoints[label],numPoints=collPoints[number]},
			Interpolation[{cp[[#]],collPoints[field][[#]]}&/@Range[numPoints],InterpolationOrder->numPoints-1]/@x
		];

	(* pointsStructure contains the lists of points corresponding to the fields in fieldList. *)
	collPoints[substitute][fieldList_List, pointsStructure_Symbol] = {
		Derivative[dz__][field_][p__] /; MemberQ[fieldList, field] :>
			collPoints[diff][pointsStructure[field], CountDerivatives[Derivative[dz][field][p],label]],
		field_[p__] /; MemberQ[fieldList,field] :> pointsStructure[field],
		label -> collPoints[label]
	};

	collPoints[substituteAnalytic][fieldList_List] := {
		Derivative[dz__][field_][p__] /; MemberQ[fieldList, field] :>
			Dot[
				collPoints[diffMatrix][CountDerivatives[Derivative[dz][field][p],label]],
				Table[field[\[FormalI]], {\[FormalI], collPoints[number]}]
			],
		field_[p__] /; MemberQ[fieldList,field] :> Table[field[\[FormalI]],{\[FormalI], collPoints[number]}],
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

Options[EvenlySpacedPointsFactory] = {Precision -> MachinePrecision};
EvenlySpacedPointsFactory[esPoints_Symbol, start_?NumberQ, end_?NumberQ, numberOfPoints_Integer, label_Symbol, OptionsPattern[]] := (
	Clear[esPoints];
	esPoints[number] = numberOfPoints;
	esPoints[precision] = OptionValue[Precision];
	esPoints[label] = Array[# &, esPoints[number], 
		{SetPrecision[start, OptionValue[Precision]], SetPrecision[end, OptionValue[Precision]]}];

	esPoints[zeroes] = SetPrecision[ConstantArray[0,esPoints[number]], OptionValue[Precision]];
	esPoints[ones] = SetPrecision[ConstantArray[1,esPoints[number]], OptionValue[Precision]];
	esPoints[spacing] = esPoints[label][[2]]-esPoints[label][[1]];

	esPoints[interpolation][ps_?ListQ] := Interpolation[Thread[({#1,#2}&)[esPoints[label],ps]]];

	esPoints[plot][ps_?ListQ, plotOptions___] := Module[{pointPairs, showList, sanitisedPlotOptions},

		pointPairs = Thread[({#1, #2}&)[esPoints[label], ps]];
		sanitisedPlotOptions = Apply[Sequence,
			DeleteCases[List[plotOptions], (ShowPoints -> _) | (ShowLine -> _)]
		];
		showList = {};

		If[(ShowPoints /. List[plotOptions]) === True, 
			AppendTo[showList, ListPlot[pointPairs, PlotStyle -> PointSize[0.02],
				sanitisedPlotOptions
			]]
		];
		If[(ShowLine /. List[plotOptions]) =!= False, 
			AppendTo[showList, 
				ListLinePlot[pointPairs, sanitisedPlotOptions]
			]
		];
		
		Show[showList, sanitisedPlotOptions]
	];
	esPoints[diff][ps_?ListQ, n_Integer /; n > 0] :=
		NDSolve`FiniteDifferenceDerivative[n, esPoints[label], ps, 
			PeriodicInterpolation -> False, "DifferenceOrder" -> 8, PeriodicInterpolation -> {False}
		];
	esPoints[diff][ps_?ListQ] := esPoints[diff][ps, 1];
	esPoints[diff][ps_?ListQ, 0] := ps;

	esPoints[diffMatrix][n_Integer /; n >= 0] :=
		NDSolve`FiniteDifferenceDerivative[{n}, {esPoints[label]}, 
			"DifferenceOrder" -> 8,
			PeriodicInterpolation -> {False}] @ "DifferentiationMatrix";

	esPoints[integrate][ps_?ListQ]:=(Head[Integrate[Interpolation[Thread[({#1,#2}&)[esPoints[label],ps]]][z],z]]/@esPoints[label]);

	esPoints[evaluate][ps_List,x_List] := Map[esPoints[interpolation][ps],x];

	esPoints[evaluate][field_Symbol,x_List] :=Map[esPoints[interpolation][esPoints[field]],x];

	(* pointsStructure contains the lists of points corresponding to the fields in fieldList. *)
	esPoints[substitute][fieldList_, pointsStructure_] = {
		Derivative[dz__][field_][p__] /; MemberQ[fieldList,field ]:>
			esPoints[diff][pointsStructure[field], CountDerivatives[Derivative[dz][field][p], label]],
		field_[p__] /; MemberQ[fieldList, field] :> pointsStructure[field],
		label->esPoints[label]
	};

	esPoints[substituteAnalytic][fieldList_List] := {
		Derivative[dz__][field_][p__] /; MemberQ[fieldList,field] :> 
			Dot[
				esPoints[diffMatrix][CountDerivatives[Derivative[dz][field][p], label]],
				Table[field[\[FormalI]], {\[FormalI], esPoints[number]}]
			],
		field_[p__] /; MemberQ[fieldList, field] :> Table[field[\[FormalI]], {\[FormalI], esPoints[number]}],
		label->esPoints[label]
	};

	esPoints[fieldTable][field_]:=Table[field[\[FormalI]],{\[FormalI],esPoints[number]}];
);

(* Domains must match up: pointsA[label][[-1]] \[Equal] pointsB[label][[1]] *)
Options[PointsPatchesFactory] = {Precision -> MachinePrecision};
PointsPatchesFactory[points_Symbol, pointsA_Symbol, pointsB_Symbol, label_Symbol, OptionsPattern[]] := (
	Clear[points];

	If[pointsA[label][[-1]] != pointsB[label][[1]], Print["Domains don't match!"]; Abort[]];

	points[label] = Join[pointsA[label][[;;-2]],pointsB[label]];
	points[number]= Length[points[label]];
	points[precision] = OptionValue[Precision];
	points[zeroes] = SetPrecision[ConstantArray[0, points[number]], OptionValue[Precision]];
	points[ones] = SetPrecision[ConstantArray[1., points[number]], OptionValue[Precision]];

	points[interpolation][ps_?ListQ] := Interpolation[Thread[({#1,#2}&)[points[label],ps]]];

	points[diff][y_?ListQ,n_Integer/;n>0] := 
		Join[
			pointsA[diff][y[[;;pointsA[number]]],n][[;;-2]],
			pointsB[diff][y[[pointsA[number];;]],n]
		];
	points[diff][y_?ListQ]:=points[diff][y,1];
	points[diffMatrix][n_Integer/;n>0] := 
		Join[
			ArrayFlatten[{{pointsA[diffMatrix][n][[;;-2]], ConstantArray[0,{pointsA[number]-1,pointsB[number]-1}]}}],
			ArrayFlatten[{{ConstantArray[0,{pointsB[number],pointsA[number]-1}], pointsB[diffMatrix][n]}}]
	];
(*		ArrayFlatten[{{pointsA[diffMatrix][n][[;;-2,;;-2]], 0}, 
			{0, pointsB[diffMatrix][n]}}
		];*)

	points[integrate][y_?ListQ] := 
		With[{integrationA = pointsA[integrate][y[[;;pointsA[number]]]]},
			Join[
				integrationA[[;;-2]],
				integrationA[[-1]]+pointsB[integrate][y[[pointsA[number];;]]]
			]
		];

	points[plot][y_?ListQ, plotOptions___] := Module[{pointPairs, showList, sanitisedPlotOptions},

		pointPairs = Thread[({#1, #2}&)[points[label], y]];
		sanitisedPlotOptions = Apply[Sequence,
			DeleteCases[List[plotOptions], (ShowPoints -> _) | (ShowLine -> _)]
		];
		showList = {};

		If[(ShowPoints /. List[plotOptions]) =!= False, 
			AppendTo[showList, ListPlot[pointPairs, PlotStyle -> PointSize[0.02],
				sanitisedPlotOptions
			]]
		];
		If[(ShowLine /. List[plotOptions]) =!= False, 
			AppendTo[showList, 
				ListLinePlot[pointPairs, sanitisedPlotOptions]
			]
		];
		
		Show[showList, sanitisedPlotOptions]
	];

	points[evaluate][ps_List,x_List] := (
		Join[
			pointsA[evaluate][ps[[;;pointsA[number]]],Select[x,#<pointsB[label][[1]]&]],
			pointsB[evaluate][ps[[pointsA[number];;]],Select[x,#>pointsB[label][[1]]&]]
		]
	);

	points[substituteAnalytic][fieldList_List] := {
		Derivative[dz__][field_][p__]/;MemberQ[fieldList, field]:>
			points[diffMatrix][CountDerivatives[Derivative[dz][field][p],label]].Table[field[\[FormalI]],{\[FormalI],points[number]}],
		field_[p__]/;MemberQ[fieldList,field]:>Table[field[\[FormalI]],{\[FormalI], points[number]}],
		label->points[label]
	};
);

(* Testing:

CollocationPointsFactory[pointsA, 0., 1., 30, z]
EvenlySpacedPointsFactory[pointsB,1., 2., 100, z]
PointsPatchesFactory[points,pointsA,pointsB,z] 

(* Diff *)
points[plot][Sin[5points[z]],PlotRange\[Rule]All]
points[plot][points[diff][Sin[5points[z]]]]
points[plot][points[diff][Sin[5points[z]]]-5Cos[5points[z]],PlotRange\[Rule]All]

points[diffMatrix][1]//MatrixPlot

f'[z]/.points[substituteAnalytic][{f}]/.f[i_]:>(points[z]^2)[[i]]
points[plot][%]
points[diffMatrix][1].(points[z]^2)
points[plot][%]

(* integration *)
points[plot][Sin[10points[z]],PlotRange\[Rule]All]
points[plot][points[integrate][Sin[10points[z]]]]
points[plot][points[integrate][Sin[10points[z]]]+0.1Cos[10points[z]]-0.1,PlotRange\[Rule]All]

points[interpolation][Sin[5points[z]]]
Plot[%[z],{z,0,2}]

points[evaluate][Sin[5points[z]],Linspace[0,2.,5000]]//ListPlot
*)

Options[CollocationPoints2DFactory] = {Precision -> MachinePrecision};
CollocationPoints2DFactory[collPoints2D_Symbol, zPoints_List, vPoints_List, 
		zLabel_Symbol, vLabel_Symbol,
		OptionsPattern[]] := (

	Clear[collPoints2D];

	collPoints2D[precision] = OptionValue[Precision];

	collPoints2D[zLabel] = SetPrecision[zPoints, OptionValue[Precision]];
	collPoints2D[vLabel] = SetPrecision[vPoints, OptionValue[Precision]];

	collPoints2D[number][zLabel] = Length[collPoints2D[zLabel]];
	collPoints2D[number][vLabel] = Length[collPoints2D[vLabel]];

	collPoints2D[grid][zLabel] = Outer[
		Times, collPoints2D[zLabel], ConstantArray[1, collPoints2D[number][vLabel]]
	];

	collPoints2D[grid][vLabel] = Outer[
		Times, ConstantArray[1, collPoints2D[number][zLabel]], collPoints2D[vLabel]
	];

	collPoints2D[zeroes] = SetPrecision[
		ConstantArray[0, {collPoints2D[number][zLabel], collPoints2D[number][vLabel]}], 
		OptionValue[Precision]
	];
	collPoints2D[ones] = SetPrecision[
		ConstantArray[1, {collPoints2D[number][zLabel], collPoints2D[number][vLabel]}], 
		OptionValue[Precision]
	];

	collPoints2D[diffMatrix][dz_Integer/;(dz>=0), dv_Integer/;(dv>=0)] := 
		collPoints2D[diffMatrix][dz, dv] =
		KroneckerProduct[
			DiffMatrixCollocationPoints[collPoints2D[zLabel], dz],
			DiffMatrixCollocationPoints[collPoints2D[vLabel], dv]
		];
	(* This code does not work due to a mathematica bug when Precision \[NotEqual] MachinePrecision. *)
		(*Normal[
			NDSolve`FiniteDifferenceDerivative[{dz, dy},
				{collPoints2D[zLabel], collPoints2D[vLabel]},
				PeriodicInterpolation -> False,
				"DifferenceOrder" -> "Pseudospectral"
			]["DifferentiationMatrix"]
		];*)

	collPoints2D[diff][dz_Integer/;(dz>=0), dv_Integer/;(dv>=0)][fieldPoints_] := Partition[
			collPoints2D[diffMatrix][dz, dv].Flatten[fieldPoints], 
			collPoints2D[number][vLabel]
		];
	(* Does not work due to a mathematica bug when Precision \[NotEqual] MachinePrecision. *)
(*		NDSolve`FiniteDifferenceDerivative[
			{dz, dy}, {collPoints2D[zLabel], collPoints2D[vLabel]},
			PeriodicInterpolation -> False, "DifferenceOrder" -> "Pseudospectral"
		][fieldPoints];
*)

	collPoints2D[analytic][field_] := Outer[
		Function[{i, j}, field[i, j]], 
		Range[Length[collPoints2D[zLabel]]], 
		Range[Length[collPoints2D[vLabel]]]
	];

	collPoints2D[plot][data_, PlotOptions___] := ListPlot3D[
			Flatten[Table[{collPoints2D[zLabel][[i]], collPoints2D[vLabel][[j]], data[[i, j]]},
				{i, collPoints2D[number][zLabel]}, {j, collPoints2D[number][vLabel]}],
			1],
			AxesLabel -> {zLabel, vLabel},
			PlotOptions
		];

	(* pointsStructure contains the lists of points corresponding to the fields in fieldList. *)
	collPoints2D[substitute][fields_List, pointsStructure_Symbol] := 
		Join[
			Map[
				(Derivative[dz_, dv_][#][zLabel, vLabel] :> 
					collPoints2D[diff][dz, dv][pointsStructure[#]])&,
				fields
			],
			Map[
				#[zLabel, vLabel] -> pointsStructure[#]&,
				fields
			],
			{zLabel -> collPoints2D[grid][zLabel]},
			{vLabel -> collPoints2D[grid][vLabel]}
		];

(*	{
		Derivative[dz__][field_][p__] /; MemberQ[fieldList, field] :>
			collPoints[diff][pointsStructure[field], CountDerivatives[Derivative[dz][field][p],label]],
		field_[p__] /; MemberQ[fieldList,field] :> pointsStructure[field],
		label -> collPoints[label]
	};*)

	collPoints2D[substituteAnalytic][fields_List]:=
		Join[
			Map[
				(Derivative[dz_, dv_][#][zLabel, vLabel] :> 
					Partition[
						Evaluate[collPoints2D[diffMatrix][dz, dv].Flatten[collPoints2D[analytic][#]]], 
						collPoints2D[number][vLabel]
					])&,
				fields
			],
			Map[
				#[zLabel, vLabel] -> collPoints2D[analytic][#]&,
				fields
			],
			{zLabel -> collPoints2D[grid][zLabel]},
			{vLabel -> collPoints2D[grid][vLabel]}
		];
);


(* Out of date. Not as new as CollocationPoints2DFactory. *)
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
				(Derivative[dz_,dv_][#][z, v]:>Partition[esPoints2D[diffMatrix][dz,dv].Flatten[esPoints2D[analytic][#]],esPoints2D[number][vLabel]])&,
				fields
			],
			Map[
				#[z,v]->esPoints2D[analytic][#]&,
				fields
			],
			{zLabel->esPoints2D[zLabel]}
		];

);
