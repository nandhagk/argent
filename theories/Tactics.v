(** * Tactics for time bounds

    This file defines the tactics that prove bounds on derived time functions.  [time_pose]
    adds the registered bound of every time function applied in the goal, [time_simpl] unfolds
    time functions whose value is a numeral, and [time_step] unfolds one time function and then
    tries [nia].  [loop_bound] and [amortise] apply the potential lemmas of Loop and Amortised.

    For example, on the goal [T_get p (set p v m) <= 5 * Pos.size_nat p] after [induction p],
    [time_step] unfolds [T_get] once, poses the induction hypothesis and the bounds of the
    callees, and closes the goal with [nia].

    Builds on: Time Loop Amortised *)

From Stdlib Require Import Lia.
From elpi Require Import elpi.
From Argent Require Import Time Loop Amortised.

(** Hints that discharge the premises of conditional bounds posed by [time_pose]. *)
Create HintDb time_inv.

(** * Constant time functions *)

Elpi Tactic time_consts.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate lp:{{
% [const-app H As R]: H is a time function whose body, applied to As, is the numeral R.
pred const-app i:term, i:list term, o:term.
const-app H As R :- head-gref H (const C), coq.gref->id (const C) Id,
  rex.match "^T_" Id, coq.env.const-body C (some Bo), strip-lams Bo As R, numeral R.

pred strip-lams i:term, i:list term, o:term.
strip-lams (fun _ _ B) [A|As] R :- !, strip-lams (B A) As R.
strip-lams R [] R.

pred numeral i:term.
numeral {{ O }} :- !.
numeral {{ S lp:N }} :- numeral N.

solve (goal _ _ Ty _ _ as G) GL :-
  ((pi h xs r\ copy (app [h|xs]) r :- const-app h xs r, !) =>
   (pi h r\ copy h r :- const-app h [] r, !) => copy Ty Ty2),
  coq.ltac.call "time_change" [trm Ty2] G GL.
}}.

(** Unfold the time functions whose body is a numeral, then reduce beta, iota and zeta. *)
Ltac time_simpl := elpi time_consts; cbn beta iota zeta.

(** * Posing bounds *)

(** Split the conjunction [H] of posed bounds into hypotheses, discharging the premises of each
    conditional bound when [assumption], [lia] or [eauto with time_inv] proves them. *)
Ltac time_split H :=
  lazymatch type of H with
  | True => clear H
  | ?A /\ ?B =>
    let Hb := fresh "Htime" in
    destruct H as [Hb H];
    repeat (specialize (Hb ltac:(solve [assumption | lia | eauto with time_inv])));
    time_split H
  end.

(** Add the proof [p] of a conjunction of bounds as separate hypotheses. *)
Ltac time_pose_conj p := let H := fresh "Htime" in pose proof p as H; time_split H.

Elpi Tactic time_pose.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate lp:{{
% [sub Ctx T S]: S is a subterm of T, closed under the binders of T, applying a time function
% that has a bound.
pred sub i:list prop, i:term, o:term.
sub Ctx (app [H|_] as T) T :- has-bound Ctx H.
sub Ctx (app L) S :- std.mem L X, sub Ctx X S.
sub Ctx (fun _ T B) S :- sub Ctx T S ; pi x\ sub Ctx (B x) S.
sub Ctx (prod _ T B) S :- sub Ctx T S ; pi x\ sub Ctx (B x) S.
sub Ctx (let _ T V B) S :- sub Ctx T S ; sub Ctx V S ; pi x\ sub Ctx (B x) S.
sub Ctx (match E _ Bs) S :- sub Ctx E S ; (std.mem Bs B, sub Ctx B S).

pred has-bound i:list prop, i:term.
has-bound Ctx H :- prover Ctx H _ _, !.

% [prover Ctx H P Ty]: P of type Ty proves forall x̄, [premises ->] H ā <= B, for the time
% function H.  It is a registered lemma, the sibling lemma T_g_le, or a quantified hypothesis
% such as an induction hypothesis.
pred prover i:list prop, i:term, o:term, o:term.
prover _ H LT Ty :- head-gref H G, bound G L, coq.env.global L LT, coq.env.typeof L Ty.
prover _ H LT Ty :- head-gref H G, G = const _, sibling G "" "_le" L,
  coq.env.global L LT, coq.env.typeof L Ty.
prover Ctx H V Ty :- std.mem Ctx (decl V _ Ty), Ty = prod _ _ _, inst-ty Ty _ C, lhs C L,
  L = app [H|_].

% [instance Ctx S P]: a bound instantiated on the arguments of S, possibly still waiting for
% premises.
pred instance i:list prop, i:term, o:term.
instance Ctx (app [H|_] as S) P :- prover Ctx H LT Ty,
  inst-ty Ty Xs C, lhs C Lhs, Lhs = S,
  determined Xs Ys, coq.mk-app LT Ys P.

pred inst-ty i:term, o:list term, o:term.
inst-ty (prod _ _ B) [X|Xs] C :- !, inst-ty (B X) Xs C.
inst-ty C [] C.

pred lhs i:term, o:term.
lhs (app [global (indt Le), L, _]) L :- coq.locate "le" (indt Le).

% The quantified variables fixed by the left-hand side, followed only by premises.
pred determined i:list term, o:list term.
determined [] [] :- !.
determined [X|Xs] [] :- var X, !, std.forall Xs var.
determined [X|Xs] [X|Ys] :- determined Xs Ys.

pred uniq i:list term, i:list term, o:list term.
uniq [] _ [] :- !.
uniq [X|Xs] Seen Ys :- std.mem! Seen X, !, uniq Xs Seen Ys.
uniq [X|Xs] Seen [X|Ys] :- uniq Xs [X|Seen] Ys.

% The instances that type-check; checked outside findall, which forbids new constraints.
pred well-typed i:list term, o:list term.
well-typed [] [].
well-typed [P|Ps] [P|Qs] :- coq.typecheck P _ ok, !, well-typed Ps Qs.
well-typed [_|Ps] Qs :- well-typed Ps Qs.

pred conj-of i:list term, o:term.
conj-of [] {{ I }}.
conj-of [P|Ps] {{ conj lp:P lp:Q }} :- conj-of Ps Q.

solve (goal Ctx _ Ty _ _ as G) GL :-
  std.findall (sub Ctx Ty S_) Subs, std.map Subs (s\ t\ s = sub _ _ t) Ts,
  std.findall (std.mem Ts T_, instance Ctx T_ P_) Insts,
  std.map Insts (i\ p\ sigma T\ i = (std.mem _ T, instance _ T p)) Ps0,
  uniq Ps0 [] Ps1, well-typed Ps1 Ps,
  (Ps = [], !, GL = [seal G] ;
   conj-of Ps Pf, std.assert-ok! (coq.elaborate-skeleton Pf _ Pf2) "time_pose",
   coq.ltac.call "time_pose_conj" [trm Pf2] G GL).
}}.

(** * Unfolding one time function *)

(** Destruct the scrutinee of every match left in the goal. *)
Ltac time_cases :=
  repeat
    match goal with
    | |- context [match ?e with _ => _ end] => destruct e
    end.

(** On the goal [t], which unfolds one time function of the original goal by one step: simplify,
    compute the specification functions, pose the callee bounds and try [nia], first as is and
    then after case analysis on the remaining matches. *)
Ltac time_step_rest t :=
  time_change t; time_simpl; cbn; elpi time_pose; cbn in *; try nia;
  try (time_cases; elpi time_pose; cbn in *; nia).

Elpi Tactic time_step.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate File argent.time.unfold.
Elpi Accumulate lp:{{
% The first time function applied in the left-hand side of the goal.
pred first-time i:term, o:gref.
first-time (app [H|_]) G :- head-gref H G, coq.gref->id G Id, rex.match "^T_" Id, !.
first-time (app L) G :- std.mem L X, first-time X G, !.

pred step i:gref, i:goal, o:list sealed-goal.
step TG (goal _ _ Ty _ _ as G) GL :- unfold-heads [TG] Ty Ty2,
  coq.ltac.call "time_step_rest" [trm Ty2] G GL.

solve (goal _ _ _ _ [trm F] as G) GL :- !, head-gref F GR,
  (lookup GR TG, ! ; coq.ltac.fail _ "time_step: no time function for" {coq.term->string F}),
  step TG G GL.
solve (goal _ _ Ty _ [] as G) GL :-
  coq.locate "le" (indt Le), Ty = app [global (indt Le), L, _], !,
  (first-time L TG, ! ; coq.ltac.fail _ "time_step: no time function in the left-hand side"),
  step TG G GL.
solve _ _ :- coq.ltac.fail _ "time_step: the goal must have the form T_f args <= bound".
}}.

(** Unfold by one step the time function on the left of a goal [T_f a <= e], or the time
    function of the given [f]; then simplify, pose the callee bounds and try [nia]. *)
Tactic Notation "time_step" := elpi time_step.
Tactic Notation "time_step" constr(f) := elpi time_step ltac_term:(f).

(** Pose the bounds of the time functions applied in the goal. *)
Tactic Notation "time_pose" := elpi time_pose.

(** * Loops and amortisation *)

(** On a goal [T_loop ... s H <= e] or [T_loop_fuel ... s <= e], apply the potential lemma
    with the invariant [Inv], the potential [Phi] and the stop cost [Tstop].  It leaves the
    continue obligation, the stop obligation and [Inv s], and tries [lia] on the remaining
    arithmetic. *)
Ltac loop_bound Inv Phi Tstop :=
  eapply PeanoNat.Nat.le_trans;
  [ first
      [ eapply (T_loop_le _ _ _ Inv Phi Tstop)
      | eapply (T_loop_fuel_le _ _ Inv Phi Tstop) ]
  | try lia ].

(** On a goal [total op T os s <= e], apply [amortised_uniform] with the invariant [Inv], the
    potential [Phi] and the amortised cost [A].  It leaves [amortised], the cap [A o s <= k]
    and [Inv s], and tries [lia] on the remaining arithmetic. *)
Ltac amortise Inv Phi A :=
  eapply PeanoNat.Nat.le_trans;
  [ eapply (amortised_uniform _ _ A Phi Inv) | try lia ].
