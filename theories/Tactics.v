(** * Tactics for time bounds

    This file defines the tactics that prove bounds on derived time functions.  [time_pose]
    adds the registered bound of every time function applied in the goal, [time_simpl] unfolds
    time functions whose value is a numeral, and [time_step] unfolds one time function and then
    tries [nia].  [loop_bound] and [amortise] apply the potential lemmas of Loop and Amortised.

    For example, on the goal [T_get p (set p v m) <= 5 * N.of_nat (Pos.size_nat p)] after
    [induction p],
    [time_step] unfolds [T_get] once, poses the induction hypothesis and the bounds of the
    callees, and closes the goal with [nia].

    Builds on: Time Loop Amortised *)

From Stdlib Require Import PeanoNat Lia NArith.
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
numeral {{ N0 }} :- !.
numeral {{ Npos lp:P }} :- pos-numeral P.

pred pos-numeral i:term.
pos-numeral {{ xH }} :- !.
pos-numeral {{ xO lp:P }} :- !, pos-numeral P.
pos-numeral {{ xI lp:P }} :- pos-numeral P.

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
% The search is deterministic and uses no findall, because type checking and unification of
% universe-polymorphic terms may declare constraints, which findall forbids.

% [subs T Acc R]: R adds to Acc the applications in T that are closed under the binders of T.
pred subs i:term, i:list term, o:list term.
subs (app L as T) Acc [T|R] :- !, subs-list L Acc R.
subs (fun _ T B) Acc R :- !, subs T Acc Acc1, under B Acc1 R.
subs (prod _ T B) Acc R :- !, subs T Acc Acc1, under B Acc1 R.
subs (let _ T V B) Acc R :- !, subs T Acc Acc1, subs V Acc1 Acc2, under B Acc2 R.
subs (match E _ Bs) Acc R :- !, subs E Acc Acc1, subs-list Bs Acc1 R.
subs _ Acc Acc.

pred subs-list i:list term, i:list term, o:list term.
subs-list [] Acc Acc.
subs-list [X|Xs] Acc R :- subs X Acc Acc1, subs-list Xs Acc1 R.

% The subterms under a binder, keeping those that do not mention the bound variable.
pred under i:(term -> term), i:list term, o:list term.
under B Acc R :- (pi x\ subs (B x) [] (L x)), keep-closed L Acc R.

pred keep-closed i:(term -> list term), i:list term, o:list term.
keep-closed (_\ []) Acc Acc :- !.
keep-closed (x\ [T|Ts x]) Acc R :- !, keep-closed Ts [T|Acc] R.
keep-closed (x\ [Y_ x|Ts x]) Acc R :- keep-closed Ts Acc R.

% [provers Ctx H Ps]: the proofs, with their types, of bounds of the form
% forall x̄, [premises ->] H ā <= B: registered lemmas, the sibling lemma T_g_le, and quantified
% hypotheses such as induction hypotheses.
pred provers i:list prop, i:term, o:list (pair term term).
provers Ctx H Ps :- global-provers H Gs, local-provers Ctx H Ls, std.append Gs Ls Ps.

pred global-provers i:term, o:list (pair term term).
global-provers H Ps :- head-gref H G, !, std.findall (bound G L_) Bs,
  std.map Bs (b\ l\ b = bound _ l) Ls0, sibling-prover G Ls0 Ls, std.map Ls lemma-prover Ps.
global-provers _ [].

pred sibling-prover i:gref, i:list gref, o:list gref.
sibling-prover G Ls [L|Ls] :- G = const _, sibling G "" "_le" L, !.
sibling-prover _ Ls Ls.

pred lemma-prover i:gref, o:pair term term.
lemma-prover L (pr LT Ty) :- coq.env.global L LT, coq.env.typeof L Ty.

pred local-provers i:list prop, i:term, o:list (pair term term).
local-provers [] _ [].
local-provers [decl V _ Ty|Ctx] H [pr V Ty|Ps] :- local-bound Ty H, !, local-provers Ctx H Ps.
local-provers [_|Ctx] H Ps :- local-provers Ctx H Ps.

pred local-bound i:term, i:term.
local-bound (prod _ _ _ as Ty) H :- inst-ty Ty _ C, lhs C L, L = app [H|_].

% [instances Ps S Acc R]: R adds to Acc each prover in Ps instantiated on the arguments of S,
% possibly still waiting for premises.
pred instances i:list (pair term term), i:term, i:list term, o:list term.
instances [] _ Acc Acc.
instances [pr LT Ty|Ps] S Acc R :- instance LT Ty S P, !, instances Ps S [P|Acc] R.
instances [_|Ps] S Acc R :- instances Ps S Acc R.

pred instance i:term, i:term, i:term, o:term.
instance LT Ty S P :- inst-ty Ty Xs C, lhs C Lhs, Lhs = S, determined Xs Ys,
  coq.mk-app LT Ys P, coq.typecheck P _ ok.

pred all-instances i:list prop, i:list term, i:list term, o:list term.
all-instances _ [] Acc Acc.
all-instances Ctx [(app [H|_] as S)|Ss] Acc R :- !, provers Ctx H Ps, instances Ps S Acc Acc1,
  all-instances Ctx Ss Acc1 R.
all-instances Ctx [_|Ss] Acc R :- all-instances Ctx Ss Acc R.

pred inst-ty i:term, o:list term, o:term.
inst-ty (prod _ _ B) [X|Xs] C :- !, inst-ty (B X) Xs C.
inst-ty C [] C.

pred lhs i:term, o:term.
lhs T L :- time-le T L.

% The quantified variables fixed by the left-hand side, followed only by premises.
pred determined i:list term, o:list term.
determined [] [] :- !.
determined [X|Xs] [] :- var X, !, std.forall Xs var.
determined [X|Xs] [X|Ys] :- determined Xs Ys.

pred uniq i:list term, i:list term, o:list term.
uniq [] _ [] :- !.
uniq [X|Xs] Seen Ys :- std.mem! Seen X, !, uniq Xs Seen Ys.
uniq [X|Xs] Seen [X|Ys] :- uniq Xs [X|Seen] Ys.

pred conj-of i:list term, o:term.
conj-of [] {{ I }}.
conj-of [P|Ps] {{ conj lp:P lp:Q }} :- conj-of Ps Q.

solve (goal Ctx _ Ty _ _ as G) GL :-
  subs Ty [] Ss0, uniq Ss0 [] Ss, all-instances Ctx Ss [] Ps0, uniq Ps0 [] Ps,
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

(** * Linear arithmetic over products

    A contract such as [T_get k m <= c_map * (bits k + 1)] multiplies an abstract constant by a
    size.  After distribution, the goal is linear in products such as [c_map * bits k], which
    [time_lin] replaces by fresh variables before it calls [lia]. *)

(** A marker for a factor whose monotone consequences are already posed. *)
Definition time_done (c : N) : Prop := True.

(** Succeed when [p] is a numeral of [positive]. *)
Ltac time_pos_numeral p :=
  lazymatch p with
  | xH => idtac
  | xO ?q => time_pos_numeral q
  | xI ?q => time_pos_numeral q
  end.

(** Succeed when [n] is a numeral of [N].  The leading [idtac] makes the match run when the
    tactic runs, so that [assert_fails] catches its failure. *)
Ltac time_numeral n :=
  idtac;
  lazymatch n with
  | N0 => idtac
  | Npos ?p => time_pos_numeral p
  end.

(** Distribute products over sums in the goal and in every hypothesis. *)
Ltac time_distribute :=
  rewrite ?N.mul_add_distr_l, ?N.mul_add_distr_r, ?N.mul_succ_r, ?N.mul_1_r,
    ?N.mul_1_l, ?N.mul_0_r, ?N.mul_0_l, ?N.add_0_l, ?N.add_0_r in *.

(** [N.of_nat] is monotone, so a hypothesis on sizes of type [nat] gives one on [N]. *)
Lemma time_of_nat_le (a b : nat) : (a <= b)%nat -> (N.of_nat a <= N.of_nat b)%N.
Proof.
  lia.
Qed.

(** Add [c * a <= c * b] for each hypothesis [a <= b] or [a < b] on [N] that mentions no
    product by [c], and [c * N.of_nat a <= c * N.of_nat b] for each such hypothesis on sizes of
    type [nat].  The new hypotheses mention a product by [c], so this runs one round. *)
Ltac time_mono_with c :=
  repeat
    match goal with
    | H : (?a <= ?b)%N |- _ =>
      assert_fails (idtac; match type of H with context [(c * _)%N] => idtac end);
      assert_fails (idtac; match goal with _ : (c * a <= c * b)%N |- _ => idtac end);
      pose proof (N.mul_le_mono_l a b c H)
    | H : (?a < ?b)%N |- _ =>
      assert_fails (idtac; match type of H with context [(c * _)%N] => idtac end);
      assert_fails (idtac; match goal with _ : (c * a <= c * b)%N |- _ => idtac end);
      pose proof (N.mul_le_mono_l a b c (N.lt_le_incl a b H))
    | H : (?a <= ?b)%nat |- _ =>
      assert_fails (idtac;
        match goal with _ : (c * N.of_nat a <= c * N.of_nat b)%N |- _ => idtac end);
      pose proof (N.mul_le_mono_l _ _ c (time_of_nat_le a b H))
    | H : (?a < ?b)%nat |- _ =>
      assert_fails (idtac;
        match goal with _ : (c * N.of_nat a <= c * N.of_nat b)%N |- _ => idtac end);
      pose proof (N.mul_le_mono_l _ _ c (time_of_nat_le a b (Nat.lt_le_incl a b H)))
    end.

(** Run [time_mono_with] once for every abstract constant [c], such as a [Parameter] of a
    signature or a definition that stays folded, that multiplies a term of the goal or of a
    hypothesis.  Factors that are not constants, such as bit lengths, get no consequences, so
    that a goal that needs [nia] reaches it quickly. *)
Ltac time_mono :=
  repeat
    match goal with
    | |- context [(?c * _)%N] =>
      is_const c;
      assert_fails (idtac; match goal with _ : time_done c |- _ => idtac end);
      time_mono_with c; assert (time_done c) by exact I
    | _ : context [(?c * _)%N] |- _ =>
      is_const c;
      assert_fails (idtac; match goal with _ : time_done c |- _ => idtac end);
      time_mono_with c; assert (time_done c) by exact I
    end.

(** Replace every product of two terms that are not numerals by a fresh variable, in the goal
    and in the hypotheses alike. *)
Ltac time_generalise :=
  repeat
    match goal with
    | |- context [(?x * ?y)%N] =>
      assert_fails (idtac; time_numeral x); assert_fails (idtac; time_numeral y);
      let v := fresh "time_prod" in
      set (v := (x * y)%N) in *; clearbody v
    | _ : context [(?x * ?y)%N] |- _ =>
      assert_fails (idtac; time_numeral x); assert_fails (idtac; time_numeral y);
      let v := fresh "time_prod" in
      set (v := (x * y)%N) in *; clearbody v
    end.

(** Succeed when an abstract constant multiplies a term of the goal or of a hypothesis. *)
Ltac time_has_const :=
  match goal with
  | |- context [(?c * _)%N] => is_const c
  | _ : context [(?c * _)%N] |- _ => is_const c
  end.

(** Close a goal that is linear over products, or fail and leave the goal as it was.  It runs
    only when an abstract constant multiplies a term, so that other goals reach [nia] at once. *)
Ltac time_lin :=
  solve [time_has_const; time_distribute; time_mono; time_distribute; time_generalise; lia].

(** A size enters a bound as [N.of_nat] of a [nat], and [cbn] turns the size of a constructor,
    such as [length (x :: l)], into a successor [S (length l)]. *)
Lemma time_of_nat_succ (n : nat) : N.of_nat (S n) = (N.of_nat n + 1)%N.
Proof.
  lia.
Qed.

(** Compute the specification functions in the goal, and keep the arithmetic of [N] folded.
    [cbn] would turn [1 + t] into a match on [t], and [N.pos p - 6] into matches on [p] over
    [Pos.sub_mask], which [lia] cannot read.  So the operations of [N] that [lia] reads stay
    folded, and so does [N.of_nat], so that [N.of_nat (S n)] becomes [N.of_nat n + 1] and not a
    positive literal over [Pos.of_succ_nat n].  Size functions such as [N.size_nat] and
    conversions such as [Z.abs_N] and [N.to_nat] still compute. *)
Ltac time_cbn :=
  cbn -[N.add N.mul N.sub N.succ N.pred N.max N.min N.div N.modulo N.pow N.of_nat];
  rewrite ?time_of_nat_succ.

(** [time_cbn] in the goal and in every hypothesis. *)
Ltac time_cbn_all :=
  cbn -[N.add N.mul N.sub N.succ N.pred N.max N.min N.div N.modulo N.pow N.of_nat] in *;
  rewrite ?time_of_nat_succ in *.

(** On the goal [t], which unfolds one time function of the original goal by one step: simplify,
    compute the specification functions, pose the callee bounds and try [time_lin] and then
    [nia], first as is and then after case analysis on the remaining matches. *)
Ltac time_step_rest t :=
  time_change t; time_simpl; time_cbn; elpi time_pose; time_cbn_all;
  try first [time_lin | nia];
  try (time_cases; elpi time_pose; time_cbn_all; first [time_lin | nia]).

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
  time-le Ty L, !,
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
  eapply N.le_trans;
  [ first
      [ eapply (T_loop_le _ _ _ Inv Phi Tstop)
      | eapply (T_loop_fuel_le _ _ Inv Phi Tstop) ]
  | try lia ].

(** On a goal [total op T os s <= e], apply [amortised_uniform] with the invariant [Inv], the
    potential [Phi], the amortised cost [A] and its cap [k].  It leaves [amortised], the cap
    [A o s <= k], [Inv s] and the arithmetic goal [k * N.of_nat (length os) + Phi s <= e], after
    trying [lia] on the last. *)
Ltac amortise Inv Phi A k :=
  eapply N.le_trans;
  [ eapply (amortised_uniform _ _ A Phi Inv k) | try lia ].
