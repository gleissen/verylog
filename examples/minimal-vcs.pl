query_naming(inv(if_inst, ex_inst, reg, done, t)).
% assignment of Y to X. (X->Y)
assign_op(X_T, Y_T) := ite(X_T=1, Y_T=1, Y_T=0).

% Some operation transforming X1 and X2 int Y. (represented by X1,X2 -O-> Y).
% We only track taint bits. Can later be modeled as uninterpreted function.
circle_op(X1_T, X2_T, Y_T) := ite((X1_T=1; X2_T=1), Y_T=1, Y_T=0).


next(IF_Inst, Ex_Inst, REG, Done, T,
     IF_Inst1, Ex_Inst1, REG1, Done1, T1) := 
   (
     % reset timer and taint IF_INST.
     Done=0, T1=0, Done1=0, IF_Inst1=1, Ex_Inst1=0, REG1=0
     % take a step and increment timer.
   ; Done=0, T1=T+1,
     % IF Stage
     IF_Inst1=0,
     % EX Stage
     assign_op(IF_Inst, Ex_Inst1),
     % WB Stage
     circle_op(Ex_Inst, 0, REG1),
     ite(REG1=1, Done1=1, Done1=Done)
   ; % done: spin.
     Done=1, T1=T, Done1=Done
   ).

% 1st try: relational invariant without synchronization.
/*
% init
inv(IF_InstL, Ex_InstL, REGL, DoneL, TL, IF_InstR, Ex_InstR, REGR, DoneR, TR) :-
	IF_InstL=0, Ex_InstL=0, REGL=0, DoneL=0, TL=0, IF_InstR=0, Ex_InstR=0, REGR=0, DoneR=0, TR=0.


% left step
inv(IF_InstL1, Ex_InstL1, REGL1, DoneL1, TL1, IF_InstR, Ex_InstR, REGR, DoneR, TR) :-
	inv(IF_InstL, Ex_InstL, REGL, DoneL, TL, IF_InstR, Ex_InstR, REGR, DoneR, TR),
	next(IF_InstL, Ex_InstL, REGL, DoneL, TL, IF_InstL1, Ex_InstL1, REGL1, DoneL1, TL1).

% right step
inv(IF_InstL, Ex_InstL, REGL, DoneL, TL, IF_InstR1, Ex_InstR1, REGR1, DoneR1, TR1) :-
	inv(IF_InstL, Ex_InstL, REGL, DoneL, TL, IF_InstR, Ex_InstR, REGR, DoneR, TR),
	next(IF_InstR, Ex_InstR, REGR, DoneR, TR, IF_InstR1, Ex_InstR1, REGR1, DoneR1, TR1).

TL=TR :- inv(IF_InstL, Ex_InstL, REGL, DoneL, TL, IF_InstR, Ex_InstR, REGR, DoneR, TR),
	DoneL=1,
	DoneR=1.
*/


inv(IF_Inst, Ex_Inst, REG, Done, T) :-
	IF_Inst=0, Ex_Inst=0, REG=0, Done=0, T=0.

inv(IF_Inst1, Ex_Inst1, REG1, Done1, T1) :-
	next(IF_Inst, Ex_Inst, REG, Done, T, IF_Inst1, Ex_Inst1, REG1, Done1, T1),
	inv(IF_Inst, Ex_Inst, REG, Done, T).

TR=2 :-
	inv(IF_InstL, Ex_InstL, REGL, DoneL, TL),
	inv(IF_InstR, Ex_InstR, REGR, DoneR, TR),
	DoneL=1, DoneR=1.