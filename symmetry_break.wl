(* ::Package:: *)

Needs["LieART`"]


IrrepSum[groups_, irreplists_, scales_] :=
    Module[{},
        Total @ MapThread[#1 ProductIrrep @@ MapThread[Irrep[#1][#2]&,
             {groups, #2}]&, {scales, irreplists}]
    ]


GetU1[term_] :=
    Module[{u1start},
        u1start = Position[NumberQ/@Dim/@List @@ term,False][[1,1]];
        List @@ term[[u1start ;; , 1]]
    ]


GetNonU1[term_] :=
    Module[{u1start},
        u1start = Position[NumberQ/@Dim/@List @@ term,False][[1,1]];
        term[[;;u1start-1]]
    ]


SumToList[sum_] :=
    Which[
        Length[sum + 1] < Length[sum],
            {1, sum}
        ,
        NumberQ @ sum[[1]],
            {sum[[1]], sum[[2]]}
        ,
        True,
            If[NumericQ @ #[[1]],
                {#[[1]], #[[2]]}
                ,
                {1, #}
            ]& /@ List @@ sum
    ]

ListToSum[list_] :=
    Total @ ({#[[1]] #[[2]]}& /@ list)[[All, 1]]

NonAbelianBreak[rep_, index_, subgroup_] :=
    Module[{newrep, listOfTermGroups, listOfTerms},
        newrep =
            If[NumberQ[Dim @ rep[[1]]],
                {rep}
                ,
                rep
            ];
        listOfTermGroups = DecomposeIrrep[#, subgroup, index]& /@ List
             @@ newrep;
        listOfTerms = Flatten[SumToList /@ listOfTermGroups, 1];
        ListToSum @ listOfTerms
    ]

IterativeNonAbelianBreak[sup_, sub_, index_, rep_] :=
    Module[{newrep},
        newrep = rep;
        Do[
            newrep =
                NonAbelianBreak[
                    newrep
                    ,
                    index
                    ,
                    If[sup - k == 1,
                        U1
                        ,
                        ProductAlgebra[Algebra[A][sup - k - 1], U1]
                    ]
                ]
            ,
            {k, sup - sub}
        ];
        newrep
    ]

NonAbelianBreakSUProduct[supgroup_, subgroup_, rep_] :=
    Module[{newrep, i},
        newrep = rep;
        i = 1; (* index of group currently being broken in rep *)
        Do[
            newrep = IterativeNonAbelianBreak[supgroup[[k]], subgroup[[k]], i, 
                newrep];
            i += 1 - KroneckerDelta[subgroup[[k]], 1]
            ,
            {k, Length @ supgroup}
        ];
        newrep
    ]

Bifundamental[groups_] :=
    Module[{groupsbar},
        groupsbar =
            If[# == 2,
                #
                ,
                Bar @ #
            ]& /@ groups;
        IrrepSum[Algebra[A][# - 1]& /@ groups, {{1, groups[[2]], groupsbar[[
            3]]}, {groupsbar[[1]], 1, groups[[3]]}, {groups[[1]], groupsbar[[2]],
             1}}, groups / Apply[GCD, groups]]
    ]

NonAbelianBreakSUProductPaired[supgroup_, subgroup_, rep_] :=
    Module[{list, brokelist, i},
        list = SumToList @ rep;
        brokelist = (SumToList @ NonAbelianBreakSUProduct[supgroup, subgroup, #]
            )& /@ list[[All, 2]];
        brokelist = If[Length@Dimensions@#==1,{#},#]&/@brokelist;
        Flatten[
            MapThread[
                Function[{origRep, brokeReps},
                    {origRep[[1]] * #[[1]], #[[2]], origRep[[2]]}& /@
                         brokeReps
                ]
                ,
                {list, brokelist}
            ]
            ,
            1
        ]
    ]


NumParticles[model_,i_,j_]:=Total[#[[i]]Times@@Dim@#[[j]]&/@model]


(*{# of terms, irrep, original term, non u1, u1 charges, U1 CHARGE FOR THIS CASE}*)

(* 4 = nonU1, 6 = U1 *)

SepChiralVL[origModel_] :=
    Module[{model, chi, vl, X, compat, big, small},
        chi = {};
        vl = {};
        model = origModel;
        While[
            Length @ model > 0
            ,
            X = model[[1]];(* current particle *)
            If[X[[6]] == 0 && Max @ Dim @ X[[4]] <= 2,
                (* VL with self *)
                AppendTo[vl, X];
                model = Delete[model, 1]
                ,
                (* NOT VL with self *)
                compat = Select[model, {Bar @ X[[4]], -X[[6]]} == #[[{
                    4, 6}]]&];(* VL pair candidates for X *)
                If[Length @ compat > 0,
                    (* exists VL pair *)
                    compat = Sort[compat, Abs @ (#1[[1]] - X[[1]]) > 
                        Abs @ (#2[[1]] - X[[1]])&]; (* sort by difference in # of factors with
                         X *)
                    If[X[[1]] <= compat[[1, 1]],
                        {big, small} = {compat[[1]], X}
                        ,
                        {big, small} = {X, compat[[1]]}
                    ];
                    AppendTo[vl, small];
                    model[[Position[model, big][[1]], 1]] += -small[[
                        1]];
                    big[[1]] = small[[1]];
                    AppendTo[vl, big];
                    model = Delete[model, Position[model, small][[1]]
                        ]
                    ,
                    (* NOT exist VL pair *)
                    AppendTo[chi, X];
                    model = Delete[model, 1];
                    
                ];
                
            ];
            model = Select[model, #[[1]] > 0&]
        ];
        (* COMBINE *)
        chi = {Total @ #[[All, 1]]} ~ Join ~ #[[1, 2 ;; ]]& /@ GatherBy[
            chi, #[[2 ;; ]]&];
        vl = {Total @ #[[All, 1]]} ~ Join ~ #[[1, 2 ;; ]]& /@ GatherBy[
            vl, #[[2 ;; ]]&];
        (* SORT *)
        chi = SortBy[chi, {-Times @@ Dim @ #[[4]]&, -Abs @ #[[6]]&, -#[[6]]&, -#[[1]]&}];
        vl = SortBy[vl, {-Times @@ Dim @ #[[4]]&, -Abs @ #[[6]]&, -#[[6]]&, -#[[1]]&}];
        {chi, vl}
    ]


AbelianBreakQ[big_,little_]:=Module[
	{bigInfo,littleTermMatches},
	bigInfo=Join[big,{GetNonU1@#[[2]],GetU1@#[[2]]}&/@big,2];
	littleTermMatches=Function[row,Intersection[Position[bigInfo[[All,4]],row[[2]]],Position[bigInfo[[All,1]],_?(#>=row[[1]]&)]]]/@little;
	If[MemberQ[littleTermMatches,{}],False,True]
]


(* big is output of NonAbelianBreakSUProductPaired, little is {# terms, irrep, u1 charge} *)
AbelianBreak[big_,little_]:=Module[
{result,bigInfo,littleTermMatches,embedCases, coefMatrices,coefSols,linSysRanks,embedInfo,extraLittleCoefs,extraLittle,embeddedLittle,beyondEmbeddedLittle,
beyondEmbeddedSplit,EWBrokenBig,EWBrokenBigInfo,EWBrokenSplit,noMCFIndices,embedParticles,beyondEmbedParticles,littleDual,noLittleDualIndices,combine,gathered},

result["start"]=Now;

(* {# of terms, irrep, original term, non u1, u1 charges} *)
bigInfo=Join[big,{GetNonU1@#[[2]],GetU1@#[[2]]}&/@big,2];
result["RE"]=bigInfo;

(* list of indices of bigSplitInfo that match non U1 content of little term for each little term *)
littleTermMatches=Function[row,Intersection[Position[bigInfo[[All,4]],row[[2]]],Position[bigInfo[[All,1]],_?(#>=row[[1]]&)]]]/@little;
result["RlittleTermMatches"]=littleTermMatches;
If[MemberQ[littleTermMatches,{}],Return[result,Module]];
(* list of lists of length little: each row is indices of big that correspond to possible identification of little with big *)
embedCases=Select[Tuples[littleTermMatches][[All,All,1]],DuplicateFreeQ];
result["NPossibleEmbed"]=Length@embedCases;
(* matrices of coefficients for linear system associated with each case in embedCases *)
coefMatrices= bigInfo[[#,5]]&/@embedCases;
result["M"]=Length@bigInfo[[1,5]];
(* solution to system of equations given by coefMatrices and little[[All,3]] *)
coefSols=Quiet[Check[LinearSolve[#,little[[All,3]]],{}]]&/@coefMatrices;
 (* combining all info regarding embedding cases *)
embedInfo=Select[Transpose@{embedCases,Complement[Range@result["numBrokenTerms"],#]&/@embedCases,coefMatrices,coefSols},#[[4]]!={}&];
result["NAB"]=Length@embedInfo;
(* adding null space dimension info: want to keep everything where null space rank > 0 *)
embedInfo=Join[embedInfo,{result["numU1Coef"]-MatrixRank@#[[3]]}&/@embedInfo,2];

embeddedLittle=bigInfo[[#[[1]]]]&/@embedInfo;
extraLittleCoefs=#[[All,1]]-little[[All,1]]&/@embeddedLittle;
extraLittle=MapThread[Select[Join[{#}&/@#1,#2[[All,2;;]],2],#[[1]]!=0&]&,{extraLittleCoefs,embeddedLittle}];
embedParticles=NumParticles[#,1,4]&/@embeddedLittle;
embeddedLittle=Join[{#}&/@little[[All,1]],#[[All,2;;]],2]&/@embeddedLittle;
embeddedLittle=MapThread[Function[{model,coefs},Join[model,{#[[5]] . coefs}&/@model,2]][#1,#2[[4]]]&,{embeddedLittle,embedInfo}];
beyondEmbeddedLittle=MapThread[Join[#1,bigInfo[[#2[[2]]]]]&,{extraLittle,embedInfo}];
beyondEmbeddedSplit=MapThread[Function[{model,coefs},SepChiralVL[Join[model,{#[[5]] . coefs}&/@model,2]]][#1,#2[[4]]]&,{beyondEmbeddedLittle,embedInfo}];
beyondEmbedParticles=NumParticles[#,1,4]&/@beyondEmbeddedLittle;

EWBrokenBig=SumToList@NonAbelianBreak[ListToSum@big,2,U1];
EWBrokenBigInfo=Join[EWBrokenBig,{0,GetNonU1@#[[2]],GetU1@#[[2]]}&/@EWBrokenBig,2];
EWBrokenSplit=Function[coefs,SepChiralVL[Join[EWBrokenBigInfo,{#[[5]] . Join[{1/2},coefs]}&/@EWBrokenBigInfo,2]]][#[[4]]]&/@embedInfo;
noMCFIndices=Flatten@Position[Length/@EWBrokenSplit[[All,1]],0];
embedInfo=embedInfo[[noMCFIndices]];
embeddedLittle=embeddedLittle[[noMCFIndices]];
beyondEmbeddedSplit=beyondEmbeddedSplit[[noMCFIndices]];
result["noMCFmodels"] = MapThread[{#1,#2,#3}&,{embeddedLittle,beyondEmbeddedSplit[[All,1]],beyondEmbeddedSplit[[All,2]]}];
result["NNoMCF"]=Length@result["noMCFmodels"];

littleDual={#[[1]],Bar@#[[2]],-#[[3]]}&/@little;
noLittleDualIndices=Flatten@Position[result["noMCFmodels"], _?(If[Length@#[[2]]==0,True,Length@Intersection[littleDual[[All,2;;]], #[[2,All,{4,6}]]]==0]&),1,Heads->False];
result["noLittleDualIndices"]=noLittleDualIndices;
result["models"]=result["noMCFmodels"][[noLittleDualIndices]];
embedInfo=embedInfo[[noLittleDualIndices]];
result["embedInfo"]=embedInfo;
result["NNoSMBar"]=Length@result["models"];

combine=MapThread[{{Total @ #[[All, 1]]} ~ Join ~ #[[1, 2 ;; ]]&/@GatherBy[#[[All,{1,4,6}]],#[[2;;]]&]&/@#1,#1,#2}&,{result["models"], result["embedInfo"]}]; 
result["combinedResults"]=combine;
gathered=GatherBy[combine,#[[1]]&];
result["gatheredModels"]=SortBy[{#[[1,1]],#[[All,2;;]]}&/@gathered,NumParticles[#[[1,2]],1,2]&]; (* "models" gathered by unique particle content *)
result["NU"]=result["gatheredModels"][[All,1]];
result["end"]=Now;
result["duration"]=result["end"]-result["start"];
result
]


AbelianBreakSM[big_]:=Module[{SM,SMBar,decomp, paired,results},
SM={{3,ProductIrrep[Irrep[SU3][3],Irrep[SU2][2]],1/6},
{3,ProductIrrep[Irrep[SU3][1],Irrep[SU2][2]],-1/2},
{3,ProductIrrep[Irrep[SU3][Bar@3],Irrep[SU2][1]],1/3},
{3,ProductIrrep[Irrep[SU3][Bar@3],Irrep[SU2][1]],-2/3},
{3,ProductIrrep[Irrep[SU3][1],Irrep[SU2][1]],1},
{3,ProductIrrep[Irrep[SU3][1],Irrep[SU2][1]],0}};
AbelianBreak[big,SM]
]


AbelianBreakSMQ[big_]:=Module[{SM,SMBar,decomp, paired,results},
SM={{3,ProductIrrep[Irrep[SU3][3],Irrep[SU2][2]],1/6},
{3,ProductIrrep[Irrep[SU3][1],Irrep[SU2][2]],-1/2},
{3,ProductIrrep[Irrep[SU3][Bar@3],Irrep[SU2][1]],1/3},
{3,ProductIrrep[Irrep[SU3][Bar@3],Irrep[SU2][1]],-2/3},
{3,ProductIrrep[Irrep[SU3][1],Irrep[SU2][1]],1},
{3,ProductIrrep[Irrep[SU3][1],Irrep[SU2][1]],0}};
AbelianBreakQ[big,SM]
]
