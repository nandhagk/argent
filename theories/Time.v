(** * Time functions

    This file defines the commands that derive a time function [T_f] from the kernel body of a
    Gallina definition [f], and the databases those commands share.  [T_f] counts the steps of
    call-by-value evaluation of [f]: one per call of a defined function or closure body.

    For example, [TimeFun length.] defines
    [T_length = fun A => fix T_length l := 1 + match l with [] => 0 | _ :: l' => T_length l' end].

    Builds on: rocq-elpi *)

From elpi Require Import elpi.

(** * Databases

    [timed f T_f] records each time function that [TimeFun] declares.  Facts recorded inside a
    functor are dropped when it ends, so the time function of a functor parameter or of a
    functor instance is found by the sibling rule instead, as the constant [T_f] beside [f].
    [prim c e] is the cost of a built-in constant, declared with [TimePrim].  [unfold c] marks a
    constant that is unfolded before translation, declared with [TimeUnfold].  [bound T_g L]
    registers a bound lemma for [time_pose], declared with [TimeBound].  [verified f] records
    that the time function found beside [f] by the sibling rule is the one derived from the body
    of [f]. *)

Elpi Db argent.time.db lp:{{
pred timed i:gref, o:gref.
pred prim o:gref, o:term.
pred unfold-const i:gref.
pred bound i:gref, o:gref.
pred verified i:gref.
}}.

(** * The translator

    The rules follow docs/design.md, section 2.  Every binder and argument position has a shape:
    [sh-irr] for types, proofs and predicates, [sh-fn Ss] for functions whose own binders have
    shapes [Ss], and [sh-val] for data.  A function argument is followed by its companion time
    function.  Shapes are computed on the callee's generic type, so that they agree with the
    type of the callee's time function. *)

Elpi File argent.time.lib lp:{{

kind shape type.
type sh-irr shape.
type sh-val shape.
type sh-fn list shape -> shape.

% Recursive heads under translation: the head term, the number of leading arguments (parameters
% and their companions) to drop, and the time function to call instead.
pred currec i:term, o:int, o:term.
% A local function variable and its companion.
pred tfun i:term, o:term.
% Test mode: errors are recorded in the safe instead of being raised.
pred expect-error o:safe.
% Audit mode: every looked-up callee is recorded in the safe.
pred callee-safe o:safe.
% The constant whose time function is being derived, the innermost one first.
pred deriving o:gref.
% Set while the time function of a callee is derived again to check it.
pred verifying.
% Capture mode: errors are recorded in the safe, with their messages, instead of being raised.
pred capture-error o:safe.
% The callees whose sibling time function this command has already checked.
pred verify-memo o:safe.

% ---------------------------------------------------------------------------------------------
% Errors

pred err i:string, i:string.
err Code Msg :- capture-error S, !, stash_in_safe S (pr Code Msg), fail.
err Code _ :- expect-error S, !, stash_in_safe S Code, fail.
err Code Msg :- coq.error {calc ("Argent [" ^ Code ^ "]: " ^ Msg)}.

pred tstr i:term, o:string.
tstr T S :- coq.term->string T S.

pred gstr i:gref, o:string.
gstr GR S :- coq.gref->string GR S.

% ---------------------------------------------------------------------------------------------
% Types, shapes and time types

pred wh i:term, o:term.
wh T R :- (T = prod _ _ _ ; T = sort _), !, R = T.
wh T R :- coq.reduction.lazy.whd T R.

pred ends-sort i:term.
ends-sort T :- wh T T1, ends-sort-whd T1.

pred ends-sort-whd i:term.
ends-sort-whd (sort _).
ends-sort-whd (prod N D B) :- pi x\ decl x N D => ends-sort (B x).

% A type is irrelevant when it is an arity or lives in Prop or SProp.
pred irr i:term.
irr D :- ends-sort D, !.
irr D :- coq.typecheck D S ok, wh S S1, (S1 = sort prop ; S1 = sort sprop), !.

pred shape-of i:term, o:shape.
% The output is unified after the cuts, so that a caller with a bound output cannot skip a guard.
shape-of D S :- irr D, !, S = sh-irr.
shape-of D S :- wh D (prod _ _ _), !, binder-shapes D Ss, S = sh-fn Ss.
shape-of _ S :- S = sh-val.

pred binder-shapes i:term, o:list shape.
binder-shapes T Ss :- wh T T1, binder-shapes-whd T1 Ss.

pred binder-shapes-whd i:term, o:list shape.
binder-shapes-whd (prod N D B) [S|Ss] :- !, shape-of D S,
  pi x\ decl x N D => binder-shapes (B x) Ss.
binder-shapes-whd _ [].

pred is-fn i:shape.
is-fn (sh-fn _).

pred tname i:name, o:name.
tname N TN :- coq.name->id N S, coq.id->name {calc ("T_" ^ S)} TN.

% [tau T Ss TT]: the time type of T, following the binder shapes Ss.
pred tau i:term, i:list shape, o:term.
tau _ [] {{ nat }} :- !.
tau T [S|Ss] R :- wh T (prod N D B), tau-binder N D S B Ss R.

pred tau-binder i:name, i:term, i:shape, i:(term -> term), i:list shape, o:term.
tau-binder N D (sh-fn Sub) B Ss (prod N D (x\ prod TN TD (_\ R x))) :- !,
  tau D Sub TD, tname N TN, pi x\ decl x N D => tau (B x) Ss (R x).
tau-binder N D _ B Ss (prod N D R) :- pi x\ decl x N D => tau (B x) Ss (R x).

% [shift Ss I J]: the structural index I of a fix becomes J once companions are inserted.
pred shift i:list shape, i:int, o:int.
shift _ 0 0 :- !.
shift [S|Ss] I J :- I1 is I - 1, shift Ss I1 J1, shift-step S J1 J.

pred shift-step i:shape, i:int, o:int.
shift-step (sh-fn _) J1 J :- !, J is J1 + 2.
shift-step _ J1 J :- J is J1 + 1.

% ---------------------------------------------------------------------------------------------
% Small term utilities

pred zero i:term.
zero {{ 0 }}.

pred plus i:term, i:term, o:term.
plus A B B :- zero A, !.
plus A B A :- zero B, !.
plus A B {{ lp:A + lp:B }}.

pred beta-app i:term, i:list term, o:term.
beta-app (fun _ _ B) [X|Xs] R :- !, beta-app (B X) Xs R.
beta-app F Xs R :- coq.mk-app F Xs R.

pred head-gref i:term, o:gref.
head-gref (global GR) GR.
head-gref (pglobal GR _) GR.

pred take-exact i:int, i:list A, o:list A.
take-exact 0 _ [] :- !.
take-exact N [X|Xs] [X|Ys] :- M is N - 1, take-exact M Xs Ys.

pred drop-n i:int, i:list A, o:list A.
drop-n 0 L L :- !.
drop-n N [_|Xs] Ys :- M is N - 1, drop-n M Xs Ys.

pred last-of i:list A, o:A.
last-of [X] X :- !.
last-of [_|Xs] X :- last-of Xs X.

pred suffix i:list string, o:list string.
suffix L L.
suffix [_|L] S :- suffix L S.

% [mk-let N T V B R]: a let, dropped when the body does not use the variable.
pred mk-let i:name, i:term, i:term, i:(term -> term), o:term.
mk-let _ _ _ B R :- B = (_\ R), !.
mk-let N T V B (let N T V B).

% ---------------------------------------------------------------------------------------------
% Lookup

% The sibling rule: [<path>.<Pre><id><Suf>], resolved through every suffix of the path of GR,
% accepted only when its own path equals the path of GR.
pred sibling i:gref, i:string, i:string, o:gref.
sibling GR Pre Suf TGR :-
  coq.gref->path GR P, coq.gref->id GR Id, Name is Pre ^ Id ^ Suf,
  suffix P Q, std.append Q [Name] L, std.string.concat "." L S,
  coq.locate-all S Locs, std.mem Locs (loc-gref TGR), coq.gref->path TGR P, !.

pred lookup i:gref, o:gref.
lookup GR TGR :- timed GR TGR, !.
lookup GR TGR :- GR = const _, sibling GR "T_" "" TGR, !.

pred record i:gref.
record GR :- callee-safe S, not verifying, !, stash_in_safe S GR.
record _.

% [check-callee GR TGR]: TGR, the time function that lookup found for the callee GR, may be
% used.  A time function recorded by TimeFun, or one without a body (a parameter of a functor),
% is used as it is.  A sibling with a body must be the one derived from the body of GR; the
% check derives it again, which checks the callees of GR in turn, and is remembered for the rest
% of the command and, through the database, for later commands.
pred check-callee i:gref, i:gref.
check-callee GR TGR :- timed GR TGR, !.
check-callee _ (const TC) :- coq.env.const-body TC none, !.
check-callee (const C) (const TC) :- alias-of C G, alias-of TC TG, lookup G TG, !,
  check-callee G TG.
check-callee GR _ :- verified GR, !.
check-callee GR _ :- verify-memo S, open_safe S Done, std.mem! Done GR, !.
check-callee GR TGR :- new_safe E, verify-callee E GR TGR, remember-verified GR.

% [alias-of C G]: the body of C is the constant G.  The constants of a module alias, such as
% [Module K := K0.], read this way, and so do [Definition f := g.] and [Definition T_f := T_g.],
% which cost what g and T_g cost, since extraction defines f as g.
pred alias-of i:constant, o:gref.
alias-of C G :- coq.env.const-body C (some Bo), (Bo = global G ; Bo = pglobal G _), !.

pred verify-callee i:safe, i:gref, i:gref.
verify-callee E GR (const TC) :- coq.env.const-body TC (some Old),
  (capture-error E => verifying => derive-owner GR (const TC) New), !,
  (coq.unify-eq Old New ok, ! ;
   err "E_CHECK" {calc ({caller-name} ^ " calls " ^ {gstr GR} ^ ", whose time function " ^
     {gstr (const TC)} ^ " differs from the one derived from its body")}).
verify-callee E GR TGR :- open_safe E Errs, first-error Errs Why,
  err "E_CHECK" {calc ({caller-name} ^ " calls " ^ {gstr GR} ^ ", whose time function " ^
    {gstr TGR} ^ " cannot be checked: " ^ Why)}.

% [derive-owner GR TGR New]: New is the time function derived for the constant beside TGR.
pred derive-owner i:gref, i:gref, o:term.
derive-owner GR TGR New :- owner GR TGR G0, derive G0 Rs, std.mem Rs (res G0 New), !.

pred caller-name o:string.
caller-name S :- deriving GR, !, gstr GR S.
caller-name "the definition".

pred first-error i:list (pair string string), o:string.
first-error [pr Code Msg|_] S :- !, S is "[" ^ Code ^ "] " ^ Msg.
first-error [] "its body cannot be translated".

pred remember-verified i:gref.
remember-verified GR :- verify-memo S, !, stash_in_safe S GR, store-verified GR.
remember-verified GR :- store-verified GR.

% A dry run of TimeFunFails declares nothing.
pred store-verified i:gref.
store-verified _ :- expect-error _, !.
store-verified GR :-
  @global! => coq.elpi.accumulate execution-site "argent.time.db" (clause _ _ (verified GR)).

pred unfold-head i:term, o:term.
unfold-head (global (const C)) Bo :- unfold-const (const C), !, coq.env.const-body C (some Bo).
unfold-head (pglobal (const C) I) Bo :- unfold-const (const C), !,
  @uinstance! I => coq.env.const-body C (some Bo).

pred wf-name i:string.
wf-name Id :- std.mem! ["Fix_F", "Fix", "Fix_F_2", "Fix2", "Fix_sub", "Fix_F_sub", "Acc_rect",
  "Acc_rec", "Acc_iter", "well_founded_induction", "well_founded_induction_type",
  "well_founded_induction_type_2"] Id.

% ---------------------------------------------------------------------------------------------
% Cost of a term in a value position: T⟦e⟧

pred cost i:term, o:term.
cost (app [H]) C :- !, cost H C.
cost (app [app L|As]) C :- !, std.append L As L2, cost (app L2) C.
cost (app [fun N T B, A|As]) C :- !, redex N T B A As R, cost R C.
cost (app [let N T V B|As]) C :- !, cost (let N T V (x\ app [B x|As])) C.
cost (app [match E R Bs|Xs]) C :- !, convoy-args Xs, costm E R Bs Xs C.
cost (app [primitive (proj _ _), S|Rest]) C :- !, proj-cost S Rest C.
cost (app [H|As]) C :- !, head-call H As C.
cost (let N T V B) C :- !, cost-let N T V B C.
cost (match E R Bs) C :- !, costm E R Bs [] C.
cost (global GR) C :- !, head-call (global GR) [] C.
cost (pglobal GR I) C :- !, head-call (pglobal GR I) [] C.
cost (fun _ _ _ as F) _ :- !,
  err "E_CLOSURE" {calc ("closure in a value position: " ^ {tstr F})}.
cost (fix _ _ _ _ as F) _ :- !,
  err "E_CLOSURE" {calc ("local fix in a value position, not applied: " ^ {tstr F})}.
cost (mfix _ _ _ as F) _ :- !,
  err "E_CLOSURE" {calc ("local fix in a value position, not applied: " ^ {tstr F})}.
cost X {{ 0 }} :- name X, !.
cost (sort _) {{ 0 }} :- !.
cost (prod _ _ _) {{ 0 }} :- !.
cost (primitive _) {{ 0 }} :- !.
cost T _ :- err "E_TERM" {calc ("unsupported term: " ^ {tstr T})}.

% A beta-redex (fun x => k) m is read as let x := m in k.  Variables, closures and irrelevant
% arguments are substituted, since evaluating them costs nothing.
pred redex i:name, i:term, i:(term -> term), i:term, i:list term, o:term.
redex _ T B A As R :- subst-ok T A, !, coq.mk-app (B A) As R.
redex N T B A As (let N T A R) :- pi x\ coq.mk-app (B x) As (R x).

pred subst-ok i:term, i:term.
subst-ok _ A :- name A, !.
subst-ok _ (fun _ _ _) :- !.
subst-ok T _ :- irr T.

pred cost-let i:name, i:term, i:term, i:(term -> term), o:term.
cost-let _ T V B C :- irr T, !, cost (B V) C.
cost-let N T V B C :- shape-of T (sh-fn Ss), !, fn-let N T V B Ss C.
cost-let N T V B C :- cost V CV,
  (pi x\ def x N T V => cost (B x) (CB x)), mk-let N T V CB L, plus CV L C.

% let g := v in b, with g a function: C⟦v⟧ + let g := v in let T_g := F⟦v⟧ in T⟦b⟧.
pred fn-let i:name, i:term, i:term, i:(term -> term), i:list shape, o:term.
fn-let N T V B Ss C :-
  fntime V Ss T CV TV, tau T Ss TT, tname N TN,
  (pi x\ def x N T V => pi tx\ def tx TN TT TV => tfun x tx => cost (B x) (CB x tx)),
  plus CV (let N T V (x\ let TN TT TV (CB x))) C.

pred convoy-args i:list term.
convoy-args Xs :- std.forall Xs (x\ sigma T\ coq.typecheck x T ok, irr T), !.
convoy-args _ :-
  err "E_MATCH_FN" "a match returns a function that is applied to data; eta-expand the match".

pred proj-cost i:term, i:list term, o:term.
proj-cost S [] C :- !, cost S C.
proj-cost S _ _ :-
  err "E_NO_TIME" {calc ("call of a function projected from the record " ^ {tstr S})}.

% ---------------------------------------------------------------------------------------------
% Calls

pred head-call i:term, i:list term, o:term.
head-call H As C :- unfold-head H Bo, !, coq.mk-app Bo As T, cost T C.
head-call H As C :-
  head-type H HTy, binder-shapes HTy HSs, std.length As N,
  (take-exact N HSs Ks, ! ;
   err "E_OVERAPP" {calc ("over-application of " ^ {tstr H} ^ ": its type has fewer " ^
     "binders than arguments, and the result of a polymorphic function cannot be called")}),
  (std.length HSs N, ! ;
   err "E_CLOSURE" {calc ("partial application of " ^ {tstr H} ^ " in a value position")}),
  check-constructor H Ks,
  args HTy Ks As CA As2,
  call H Ks As2 CC, plus CA CC C.

pred head-type i:term, o:term.
head-type H Ty :- coq.typecheck H Ty ok, !.
head-type H _ :- err "E_TERM" {calc ("cannot type the head " ^ {tstr H})}.

pred check-constructor i:term, i:list shape.
check-constructor H Ks :- head-gref H (indc _), std.exists Ks is-fn, !,
  err "E_CLOSURE_DATA" {calc ("closure stored in data, constructor " ^ {tstr H})}.
check-constructor _ _.

% [args HTy Ks As C As2]: the cost C of evaluating the arguments As, and As2, the arguments
% with a companion inserted after each function argument.
pred args i:term, i:list shape, i:list term, o:term, o:list term.
args _ [] [] {{ 0 }} [] :- !.
args HTy [S|Ss] [A|As] C As2 :- wh HTy (prod _ D B),
  arg S D A CA As2a, args (B A) Ss As C0 As2b, plus CA C0 C, std.append As2a As2b As2.

pred arg i:shape, i:term, i:term, o:term, o:list term.
arg sh-irr _ A {{ 0 }} [A] :- !.
arg (sh-fn Sub) D A CA [A, TA] :- !, fntime A Sub D CA TA.
arg sh-val D A CA [A] :- val-arg D A CA.

pred val-arg i:term, i:term, o:term.
val-arg D _ {{ 0 }} :- irr D, !.
val-arg D A _ :- wh D (prod _ _ _), !,
  err "E_CLOSURE_DATA" {calc ("closure stored in data: " ^ {tstr A} ^
    " is passed where the callee expects data of type " ^ {tstr D})}.
val-arg _ A C :- cost A C.

% [call H Ks As2 R]: the cost of the call itself, given the arguments with companions.
pred call i:term, i:list shape, i:list term, o:term.
call H _ _ {{ 0 }} :- head-gref H (indc _), !.
call H _ As2 R :- currec H Nc TF, !, drop-n Nc As2 Rest, beta-app TF Rest R.
call H Ks _ {{ 0 }} :- head-gref H (const _), std.forall Ks (k\ k = sh-irr), !.
call H _ As2 R :- head-gref H GR, lookup GR TGR, !, check-callee GR TGR, record GR,
  coq.env.global TGR TH, coq.mk-app TH As2 R.
call H _ As2 R :- tfun H TH, !, coq.mk-app TH As2 R.
call H _ As2 R :- head-gref H GR, prim GR E, !, record GR, beta-app E As2 R.
call H _ As2 R :- local-fix-time H TH, !, coq.mk-app TH As2 R.
call H _ _ _ :- no-time H.

pred no-time i:term.
no-time H :- head-gref H (const C), coq.env.opaque? C, !,
  err "E_OPAQUE" {calc ("the opaque constant " ^ {tstr H} ^
    " has no time function; make it transparent or declare its cost with TimePrim" ^
    {functor-hint})}.
no-time H :- head-gref H (const C), coq.env.section-variables Vs, std.mem! Vs C, !,
  err "E_SECTION" {calc ("call of the section variable " ^ {tstr H} ^
    "; make it a functor parameter or run TimeFun after the section is closed")}.
no-time H :- head-gref H GR, coq.gref->id GR Id, wf-name Id, !,
  err "E_WF" {calc ("well-founded recursion through " ^ {tstr H} ^
    " is not supported; use Argent.Loop.loop or loop_fuel")}.
no-time H :- head-gref H (const C), coq.env.const C none _, !,
  err "E_NO_TIME" {calc ("no time function for " ^ {tstr H} ^
    ", which has no body; declare its cost with TimePrim" ^ {functor-hint})}.
no-time H :- head-gref H _, !,
  err "E_NO_TIME" {calc ("no time function for " ^ {tstr H} ^ "; run TimeFun on it first" ^
    {functor-hint})}.
no-time H :- name H, !,
  err "E_NO_TIME" {calc ("call of the local function " ^ {tstr H} ^
    ", which has no time function (a closure stored in data?)")}.
no-time H :- err "E_NO_TIME" {calc ("call of " ^ {tstr H} ^ ", which has no time function")}.

% rocq-elpi gives no way to tell that a command runs inside a functor, where the facts that
% TimeFun, TimePrim, TimeUnfold and TimeBound record are dropped at its end, so the message of a
% missing time function names that cause.
pred functor-hint o:string.
functor-hint S :- S is "; a TimeFun for a constant of another library, a TimePrim or a " ^
  "TimeUnfold that ran inside a functor is lost at the end of the functor, so run it outside".

% ---------------------------------------------------------------------------------------------
% Function values: C⟦e⟧ and F⟦e⟧, for a slot whose binders have shapes Ss and whose
% instantiated type is D.

pred fntime i:term, i:list shape, i:term, o:term, o:term.
fntime X _ _ {{ 0 }} TX :- tfun X TX, !.
fntime (app [H]) Ss D C F :- !, fntime H Ss D C F.
fntime (app [app L|As]) Ss D C F :- !, std.append L As L2, fntime (app L2) Ss D C F.
fntime (app [fun N T B, A|As]) Ss D C F :- !, redex N T B A As R, fntime R Ss D C F.
fntime (app [let N T V B|As]) Ss D C F :- !, fntime (let N T V (x\ app [B x|As])) Ss D C F.
fntime (let N T V B) Ss D C F :- !, fn-let-val N T V B Ss D C F.
fntime (fun _ _ _ as L) Ss D {{ 0 }} F :- !, eta Ss D [] [] (lam-body L) F.
fntime (match _ _ _ as M) _ _ _ _ :- !,
  err "E_MATCH_FN" {calc ("a match returns a function; eta-expand it: " ^ {tstr M})}.
fntime (app [match _ _ _|_] as M) _ _ _ _ :- !,
  err "E_MATCH_FN" {calc ("a match returns a function; eta-expand it: " ^ {tstr M})}.
fntime (app [primitive (proj _ _)|_] as P) _ _ _ _ :- !,
  err "E_NO_TIME" {calc ("a function projected from a record has no time function: " ^
    {tstr P})}.
fntime (app [H|As]) Ss D C F :- !, partial-app H As Ss D C F.
fntime H Ss D C F :- partial-app H [] Ss D C F.

pred fn-let-val i:name, i:term, i:term, i:(term -> term), i:list shape, i:term, o:term,
  o:term.
fn-let-val _ T V B Ss D C F :- irr T, !, fntime (B V) Ss D C F.
fn-let-val N T V B Ss D C F :- shape-of T sh-val, !, cost V CV,
  (pi x\ def x N T V => fntime (B x) Ss D (CX x) (FX x)),
  mk-let N T V CX CL, plus CV CL C, mk-let N T V FX F.
fn-let-val _ _ _ _ _ _ _ _ :-
  err "E_TERM" "a let of a function in a function position is not supported".

% Partial application h ā: the arguments are paid once, when the closure is created.
pred partial-app i:term, i:list term, i:list shape, i:term, o:term, o:term.
partial-app H As Ss D C F :- unfold-head H Bo, !, coq.mk-app Bo As T, fntime T Ss D C F.
partial-app H As Ss D C F :-
  head-type H HTy, binder-shapes HTy HSs, std.length As N,
  (take-exact N HSs Ks, ! ;
   err "E_OVERAPP" {calc ("over-application of " ^ {tstr H})}),
  check-constructor H Ks,
  args HTy Ks As C _,
  partial-body H As K,
  eta Ss D [] [] K F.

pred partial-body i:term, i:list term, o:(pred i:list term, i:list term, o:term).
partial-body H _ (_\ _\ r\ r = {{ 1 }}) :- head-gref H (indc _), !.
partial-body H As (xs\ _\ r\ full-call H As xs r).

% The call cost of h (ā ++ x̄), with the cost of ā already paid at closure creation.
pred full-call i:term, i:list term, i:list term, o:term.
full-call H As Xs R :-
  std.append As Xs All, head-type H HTy, binder-shapes HTy HSs, std.length All N,
  (take-exact N HSs Ks, ! ; err "E_OVERAPP" {calc ("over-application of " ^ {tstr H})}),
  args HTy Ks All _ As2, call H Ks As2 R.

pred lam-body i:term, i:list term, i:list term, o:term.
lam-body L Xs _ R :- coq.mk-app L Xs T, cost T C, plus {{ 1 }} C R.

% [eta Ss D Xs Xps K F]: λ x̄⁺ over the binders of D with shapes Ss, then K x̄ x̄⁺.
pred eta i:list shape, i:term, i:list term, i:list term,
  i:(pred i:list term, i:list term, o:term), o:term.
eta [] _ Xs Xps K R :- !, K Xs Xps R.
eta [S|Ss] D Xs Xps K R :- wh D (prod N Dx B), eta-binder N Dx S B Ss Xs Xps K R.

pred eta-binder i:name, i:term, i:shape, i:(term -> term), i:list shape, i:list term,
  i:list term, i:(pred i:list term, i:list term, o:term), o:term.
eta-binder N Dx (sh-fn Sub) B Ss Xs Xps K (fun N Dx R) :- !, tau Dx Sub TD, tname N TN,
  pi x\ decl x N Dx => (R x = fun TN TD (R1 x),
    pi tx\ decl tx TN TD => tfun x tx =>
      eta Ss (B x) {std.append Xs [x]} {std.append Xps [x, tx]} K (R1 x tx)).
eta-binder N Dx _ B Ss Xs Xps K (fun N Dx R) :-
  pi x\ decl x N Dx => eta Ss (B x) {std.append Xs [x]} {std.append Xps [x]} K (R x).

% ---------------------------------------------------------------------------------------------
% Matches

pred costm i:term, i:term, i:list term, i:list term, o:term.
costm E Rty Bs Xs C :-
  std.length Xs K, scrut-cost E CE, retnat K Rty Rty2 I,
  coq.env.indt I _ NP _ _ _ KTs,
  std.map KTs (kt\ n\ sigma M\ nprods kt M, n is M - NP) Ar,
  std.map2 Ar Bs (a\ b\ c\ br a K b c) Bs2,
  match-result E Rty2 Bs2 Xs M, plus CE M C.

pred scrut-cost i:term, o:term.
scrut-cost E {{ 0 }} :- coq.typecheck E T ok, irr T, !.
scrut-cost E C :- cost E C.

pred match-result i:term, i:term, i:list term, i:list term, o:term.
match-result _ _ Bs _ {{ 0 }} :- std.forall Bs zb, !.
match-result E R Bs Xs M :- coq.mk-app (match E R Bs) Xs M.

pred zb i:term.
zb (fun _ _ B) :- !, pi x\ zb (B x).
zb Z :- zero Z.

pred nprods i:term, o:int.
nprods (prod _ _ B) N :- !, pi x\ nprods (B x) M, N is M + 1.
nprods _ 0.

pred ind-of i:term, o:inductive.
ind-of (global (indt I)) I.
ind-of (pglobal (indt I) _) I.
ind-of (app [global (indt I)|_]) I.
ind-of (app [pglobal (indt I) _|_]) I.

% The return clause becomes nat (or Π ȳ. nat for a convoy of K proofs).
pred retnat i:int, i:term, o:term, o:inductive.
retnat K (fun N T B) (fun N T R) I :- (pi x\ sigma A B1 C1\ B x = fun A B1 C1), !,
  pi x\ decl x N T => retnat K (B x) (R x) I.
retnat K (fun N T B) (fun N T R) I :- wh T Ti, ind-of Ti I, !,
  pi x\ decl x N T => retk K (B x) (R x).
retnat _ R _ _ :- err "E_TERM" {calc ("unsupported match return clause: " ^ {tstr R})}.

pred retk i:int, i:term, o:term.
retk 0 T _ :- wh T (prod _ _ _), not (ends-sort T), !,
  err "E_MATCH_FN" {calc ("a match returns a function of type " ^ {tstr T} ^
    "; eta-expand the match")}.
retk 0 _ {{ nat }} :- !.
retk K T (prod N D R) :- wh T (prod N D B), !, K1 is K - 1,
  pi x\ decl x N D => retk K1 (B x) (R x).
retk _ T _ :- err "E_TERM" {calc ("unsupported convoy return type: " ^ {tstr T})}.

pred br i:int, i:int, i:term, o:term.
br 0 0 B C :- !, cost B C.
br 0 K (fun Na T B) (fun Na T C) :- !, K1 is K - 1, pi x\ decl x Na T => br 0 K1 (B x) (C x).
br N K (fun Na T B) (fun Na T C) :- N > 0, !, M is N - 1,
  pi x\ decl x Na T => br M K (B x) (C x).
br _ _ B _ :- err "E_TERM" {calc ("unsupported match branch: " ^ {tstr B})}.

% ---------------------------------------------------------------------------------------------
% Fixpoints

kind member type.
% mem Key Value Nc: a member of a fix block, the head term that calls it, the value that
% replaces its variable, and the number of leading arguments to drop from calls of Key.
type mem term -> term -> int -> member.

% [fix-body Bo TBo]: the body of a recursive function, its binders followed by 1 + T⟦body⟧.
pred fix-body i:term, o:term.
fix-body (fun N D B) R :- !, shape-of D S, fix-binder N D S B R.
fix-body Bo R :- body-time Bo R.

pred fix-binder i:name, i:term, i:shape, i:(term -> term), o:term.
fix-binder N D (sh-fn Sub) B (fun N D R) :- !, tau D Sub TD, tname N TN,
  pi x\ decl x N D => (R x = fun TN TD (R1 x),
    pi tx\ decl tx TN TD => tfun x tx => fix-body (B x) (R1 x tx)).
fix-binder N D _ B (fun N D R) :- pi x\ decl x N D => fix-body (B x) (R x).

% The base of a function: 1 + T⟦body⟧, or, when the body returns a function,
% λ x̄⁺. 1 + C⟦body⟧ + F⟦body⟧ x̄⁺.
pred body-time i:term, o:term.
body-time Bo R :- head-type Bo Ty, binder-shapes Ty Ss, body-time-ss Bo Ty Ss R.

pred body-time-ss i:term, i:term, i:list shape, o:term.
body-time-ss Bo _ [] R :- !, cost Bo C, plus {{ 1 }} C R.
body-time-ss Bo Ty Ss R :- fntime Bo Ss Ty C F, eta Ss Ty [] [] (eta-top C F) R.

pred eta-top i:term, i:term, i:list term, i:list term, o:term.
eta-top C F _ Xps R :- beta-app F Xps FX, plus C FX R0, plus {{ 1 }} R0 R.

pred tfix i:name, i:int, i:term, i:(term -> term), i:term, i:term, i:int, o:term.
tfix N I Ty B Key Val Nc (fix TN I2 TTy R) :-
  binder-shapes Ty Ss, tau Ty Ss TTy, shift Ss I I2, tname N TN,
  pi tf\ decl tf TN TTy => currec Key Nc tf => fix-body (B Val) (R tf).

pred tblock i:list member, i:mfix-block, o:mfix-block.
tblock [mem K V Nc|Ms] (mfix-ty N R Ty B) (mfix-ty TN R2 TTy TB) :- !,
  binder-shapes Ty Ss, tau Ty Ss TTy, shift Ss R R2, tname N TN,
  pi tf\ decl tf TN TTy => currec K Nc tf => tblock Ms (B V) (TB tf).
tblock [] (mfix-bo Bs) (mfix-bo TBs) :- std.map Bs fix-body TBs.

% The names and structural indices of the members of a block.
pred block-names i:mfix-block, o:list name, o:list int.
block-names (mfix-ty N R _ B) [N|Ns] [R|Rs] :- pi f\ block-names (B f) Ns Rs.
block-names (mfix-bo _) [] [].

pred block-rno i:mfix-block, i:int, o:int.
block-rno (mfix-ty _ R _ _) 0 R :- !.
block-rno (mfix-ty _ _ _ B) J R :- J1 is J - 1, pi f\ block-rno (B f) J1 R.

% A local fix in head position: its time function is the translated fix.
pred local-fix-time i:term, o:term.
local-fix-time (fix N I Ty B as F) TF :- !, tfix N I Ty B F F 0 TF.
local-fix-time (mfix J _ Blk) (mfix J I2 TBlk) :-
  block-names Blk Ns Rs, local-members Blk 0 Ns Rs Ms,
  tblock Ms Blk TBlk, block-rno TBlk J I2.

pred local-members i:mfix-block, i:int, i:list name, i:list int, o:list member.
local-members _ _ [] [] [] :- !.
local-members Blk K [_|Ns] [R|Rs] [mem (mfix K R Blk) (mfix K R Blk) 0|Ms] :-
  K1 is K + 1, local-members Blk K1 Ns Rs Ms.

% ---------------------------------------------------------------------------------------------
% The top-level rule

kind result type.
% res F TBo: the body of the time function of the constant F.
type res gref -> term -> result.

% [lams F Ps Nc Target Bo TBo Ms]: Bo is the body of the definition whose head term is F, under
% the parameters Ps, which with their companions number Nc.  For a mutual block, Target selects
% the member to translate (none: the member that F names), and Ms lists the members that have a
% constant, with their index in the block.
pred lams i:term, i:list term, i:int, i:option int, i:term, o:term, o:list (pair int gref).
lams F Ps Nc T (fun N D B) R Ms :- !, shape-of D S, lam-binder F Ps Nc T N D S B R Ms.
lams F Ps Nc _ (fix N I Ty B) R [pr 0 GR] :- !, head-gref F GR,
  coq.mk-app F Ps V, tfix N I Ty B F V Nc R.
lams F Ps Nc T (mfix J _ Blk) (mfix TI I2 TBlk) Ms :- !,
  block-names Blk Ns Rs, head-gref F GR,
  top-members GR F Ps Nc Blk J 0 Ns Rs Mems Ms, tblock Mems Blk TBlk,
  target-index T J TI, block-rno TBlk TI I2.
lams F _ _ _ Bo R [pr 0 GR] :- head-gref F GR, body-time Bo R.

pred target-index i:option int, i:int, o:int.
target-index none J J.
target-index (some K) _ K.

pred lam-binder i:term, i:list term, i:int, i:option int, i:name, i:term, i:shape,
  i:(term -> term), o:term, o:list (pair int gref).
lam-binder F Ps Nc T N D (sh-fn Sub) B (fun N D R) Ms :- !, tau D Sub TD, tname N TN,
  Nc2 is Nc + 2,
  pi x\ decl x N D => (R x = fun TN TD (R1 x),
    pi tx\ decl tx TN TD => tfun x tx =>
      lams F {std.append Ps [x]} Nc2 T (B x) (R1 x tx) Ms).
lam-binder F Ps Nc T N D _ B (fun N D R) Ms :- Nc1 is Nc + 1,
  pi x\ decl x N D => lams F {std.append Ps [x]} Nc1 T (B x) (R x) Ms.

% Each member of a top-level mutual block is replaced by its own constant, found by the
% sibling rule on the name of its fix binder, or else by the closed fix term itself.
pred top-members i:gref, i:term, i:list term, i:int, i:mfix-block, i:int, i:int, i:list name,
  i:list int, o:list member, o:list (pair int gref).
top-members _ _ _ _ _ _ _ [] [] [] [] :- !.
top-members GR F Ps Nc Blk J K [N|Ns] [R|Rs] [M|Mems] Ms :-
  member-of GR F Ps Nc Blk J K N R M Found, K1 is K + 1,
  top-members GR F Ps Nc Blk J K1 Ns Rs Mems Ms0, std.append Found Ms0 Ms.

pred member-of i:gref, i:term, i:list term, i:int, i:mfix-block, i:int, i:int, i:name, i:int,
  o:member, o:list (pair int gref).
member-of GR F Ps Nc _ J J _ _ (mem F V Nc) [pr J GR] :- !, coq.mk-app F Ps V.
member-of GR _ Ps Nc Blk _ K N R (mem G V Nc) [pr K SGR] :-
  coq.name->id N Id, coq.gref->path GR P, std.append P [Id] L, std.string.concat "." L S,
  coq.locate-all S Locs, std.mem Locs (loc-gref SGR), SGR = const SC,
  coq.gref->path SGR P, coq.env.const-body SC (some SBo),
  strip-params Ps SBo (mfix K R Blk), !,
  coq.env.global SGR G, coq.mk-app G Ps V.
member-of _ _ _ _ Blk _ K _ R (mem (mfix K R Blk) (mfix K R Blk) 0) [].

% [strip-params Ps Bo M]: Bo applied to the parameters Ps is convertible to M.
pred strip-params i:list term, i:term, i:term.
strip-params [] Bo M :- coq.unify-eq Bo M ok.
strip-params [P|Ps] (fun _ _ B) M :- strip-params Ps (B P) M.

% [derive GR Rs]: the time function bodies for GR and for the other members of its block.
pred derive i:gref, o:list result.
derive GR Rs :-
  GR = const C, coq.env.global GR F, const-body-at F C Bo,
  deriving GR => (lams F [] 0 none Bo R0 Ms, derive-others F Bo GR R0 Ms Rs).

pred const-body-at i:term, i:constant, o:term.
const-body-at (pglobal _ I) C Bo :- !, @uinstance! I => coq.env.const-body C (some Bo).
const-body-at _ C Bo :- coq.env.const-body C (some Bo).

pred derive-others i:term, i:term, i:gref, i:term, i:list (pair int gref), o:list result.
derive-others _ _ _ _ [] [] :- !.
derive-others F Bo GR R0 [pr _ GR|Ms] [res GR R0|Rs] :- !, derive-others F Bo GR R0 Ms Rs.
derive-others F Bo GR R0 [pr K G|Ms] [res G R|Rs] :-
  lams F [] 0 (some K) Bo R _, derive-others F Bo GR R0 Ms Rs.

% ---------------------------------------------------------------------------------------------
% Checks before translation

pred check-code i:gref, o:constant.
check-code (const C) C :- coq.env.opaque? C, !,
  err "E_OPAQUE" {calc ("cannot derive a time function for the opaque constant " ^
    {gstr (const C)})}.
check-code (const C) C :- coq.env.const C none _, !,
  err "E_OPAQUE" {calc ({gstr (const C)} ^ " has no body (an axiom or a parameter)")}.
check-code (const C) C :- coq.env.typeof (const C) Ty, irr Ty, !,
  err "E_NOT_CODE" {calc ({gstr (const C)} ^ " is a type, a predicate or a proof")}.
check-code (const C) C :- !.
check-code GR _ :- err "E_NOT_CODE" {calc ({gstr GR} ^ " is not a defined constant")}.

pred check-untimed i:gref.
check-untimed GR :- lookup GR TGR, !,
  err "E_TIMED" {calc ({gstr GR} ^ " already has the time function " ^ {gstr TGR})}.
check-untimed GR :- prim GR _, !,
  err "E_TIMED" {calc ({gstr GR} ^ " already has a cost declared with TimePrim")}.
check-untimed _.

% A definition that uses a section variable changes arity when the section closes.
pred check-section i:constant.
check-section C :- coq.env.section-variables Vs, std.mem Vs V,
  coq.env.const-body C (some Bo), coq.env.term-dependencies Bo Deps,
  coq.gref.set.mem (const V) Deps, !, coq.env.typeof (const V) VTy, shape-of VTy S,
  section-kind S Kind,
  err "E_SECTION" {calc ({gstr (const C)} ^ " uses the " ^ Kind ^ " section variable " ^
    {gstr (const V)} ^ "; make it a functor parameter or run TimeFun after the section")}.
check-section _.

pred section-kind i:shape, o:string.
section-kind (sh-fn _) "function-typed" :- !.
section-kind _ "data".

% A time function lives beside its constant; for a constant of another module it lives in a
% module named like the last component of that constant's path.
pred check-placement i:gref.
check-placement GR :- coq.gref->path GR P, coq.env.current-path P, !.
check-placement GR :- coq.gref->path GR P, last-of P M, coq.env.current-path CP,
  last-of CP M, !.
check-placement GR :- coq.gref->path GR P, last-of P M,
  err "E_PLACE" {calc ("the time function of " ^ {gstr GR} ^
    " belongs beside it; for a constant of another library, run TimeFun inside a module " ^
    "named " ^ M)}.

% ---------------------------------------------------------------------------------------------
% Declaring time functions

pred check-typed i:gref, i:term, o:term.
check-typed _ TBo Ty :- coq.typecheck TBo Ty ok, !.
check-typed GR TBo _ :- coq.typecheck TBo _ (error Msg), !,
  err "E_ILLTYPED" {calc ("the time function of " ^ {gstr GR} ^ " is ill-typed: " ^ Msg ^
    "; a function was probably passed where a polymorphic callee expects data")}.

pred declare i:result, o:pair gref gref.
declare (res GR TBo) (pr GR (const TC)) :-
  check-typed GR TBo Ty, coq.gref->id GR Id, TId is "T_" ^ Id,
  add-time-const GR TId TBo Ty TC,
  copy-implicits GR (const TC),
  (@global! => coq.arguments.set-simplification (const TC) never),
  @global! => coq.elpi.accumulate execution-site "argent.time.db"
    (clause _ _ (timed GR (const TC))).

pred add-time-const i:gref, i:id, i:term, i:term, o:constant.
add-time-const GR TId TBo Ty TC :- coq.env.univpoly? GR _, !,
  @univpoly! => coq.env.add-const TId TBo Ty @transparent! TC.
add-time-const _ TId TBo Ty TC :- coq.env.add-const TId TBo Ty @transparent! TC.

% A time function never unfolds under cbn and simpl, so that a plain cbn in a proof computes the
% specification functions and leaves every callee time function folded, where its bound applies.
% The tactics time_unfold and time_step unfold time functions one step at a time.

% T_f copies the implicit status of f, and every companion is explicit.
pred copy-implicits i:gref, i:gref.
copy-implicits GR TGR :- coq.arguments.implicit GR [Imps|_], !,
  coq.env.typeof GR Ty, binder-shapes Ty Ss, with-companions Ss Imps Out,
  @global! => coq.arguments.set-implicit TGR [Out].
copy-implicits _ _.

pred with-companions i:list shape, i:list implicit_kind, o:list implicit_kind.
with-companions [] _ [] :- !.
with-companions [S|Ss] [] Out :- !, with-companions [S|Ss] [explicit] Out.
with-companions [sh-fn _|Ss] [I|Is] [I, explicit|Out] :- !, with-companions Ss Is Out.
with-companions [_|Ss] [I|Is] [I|Out] :- with-companions Ss Is Out.

% [timefun S Ns]: derive and declare the time functions; Ns pairs each constant with its new
% time function, so that later arguments of the same command can see them.
pred timefun i:string, o:list (pair gref gref).
timefun S Ns :-
  coq.locate S GR, check-code GR C, check-untimed GR, check-section C, check-placement GR,
  derive GR Rs, std.forall Rs check-untimed-res, std.map Rs declare Ns.

pred check-untimed-res i:result.
check-untimed-res (res GR _) :- check-untimed GR.

% ---------------------------------------------------------------------------------------------
% Checking and bounds

% [owner GR TGR G0]: the constant beside the time function TGR with the name of GR.  A module
% alias such as the parameter of a functor instance names the same constant as G0, but Elpi
% reads its body as a call of G0.
pred owner i:gref, i:gref, o:gref.
owner GR TGR G0 :- coq.gref->path TGR P, coq.gref->id GR Id, std.append P [Id] L,
  std.string.concat "." L S, coq.locate-all S Locs, std.mem Locs (loc-gref G0),
  coq.gref->path G0 P, !.
owner GR _ GR.

pred timecheck i:gref.
timecheck GR :- lookup GR (const TC), coq.env.const-body TC (some Old), !,
  owner GR (const TC) G0, derive G0 Rs, std.mem Rs (res G0 New), !,
  (coq.unify-eq Old New ok, ! ;
   err "E_CHECK" {calc ("TimeCheck: the stored time function of " ^ {gstr GR} ^
     " differs from the derived one")}).
timecheck GR :- lookup GR _, !,
  err "E_CHECK" {calc ("TimeCheck: the time function of " ^ {gstr GR} ^ " has no body")}.
timecheck GR :- err "E_CHECK" {calc ("TimeCheck: " ^ {gstr GR} ^ " has no time function")}.

% [bound-head Ty TG]: Ty is forall x̄, [P x̄ ->] T_g ā <= B, and TG is T_g.
pred bound-head i:term, o:gref.
bound-head (prod N D B) G :- !, pi x\ decl x N D => bound-head (B x) G.
bound-head (app [global (indt Le), L, _]) G :- coq.locate "le" (indt Le), head-gref-app L G, !.
bound-head _ _ :- coq.error "TimeBound: the conclusion must have the form T_g args <= bound".

pred head-gref-app i:term, o:gref.
head-gref-app (app [H|_]) G :- head-gref H G.
head-gref-app H G :- head-gref H G.

}}.

(** * Commands *)

(** [TimeFun f g ...] derives [T_f], [T_g], ...  For a mutual block it derives a time function
    for every member that is a constant. *)

Elpi Command TimeFun.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate lp:{{
main Args :- new_safe M, verify-memo M => time-args Args.

pred time-args i:list argument.
time-args [] :- !.
time-args [str S|As] :- !, timefun S Ns, with-timed Ns As.
time-args [A|_] :- coq.error "TimeFun: expected constant names, got" A.

pred with-timed i:list (pair gref gref), i:list argument.
with-timed [] As :- time-args As.
with-timed [pr G T|Ns] As :- timed G T => with-timed Ns As.
}}.

Elpi Export TimeFun.

(** [TimeCheck f] re-runs the translation of [f] and requires the result to be convertible with
    the stored [T_f], so that a time function cannot be edited by hand. *)

Elpi Command TimeCheck.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate lp:{{
main Args :- new_safe M, verify-memo M => std.forall Args check-arg.

pred check-arg i:argument.
check-arg (str S) :- !, coq.locate S GR, timecheck GR.
check-arg A :- coq.error "TimeCheck: expected constant names, got" A.
}}.

Elpi Export TimeCheck.

(** [TimeAudit r ...] walks every constant that the roots call, transitively, and fails on a
    computational constant that has neither a time function nor a [TimePrim] cost.  It also runs
    [TimeCheck] on every time function it meets. *)

Elpi Command TimeAudit.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate lp:{{
main Args :- std.map Args root-gref Roots, new_safe M, (verify-memo M => audit Roots [] N),
  coq.say "TimeAudit: checked" N "time functions".

pred root-gref i:argument, o:gref.
root-gref (str S) GR :- !, coq.locate S GR.
root-gref A _ :- coq.error "TimeAudit: expected constant names, got" A.

pred audit i:list gref, i:list gref, o:int.
audit [] Seen N :- !, std.length Seen N.
audit [G|Gs] Seen N :- std.mem! Seen G, !, audit Gs Seen N.
audit [G|Gs] Seen N :- audit-one G Callees, std.append Gs Callees Gs2, audit Gs2 [G|Seen] N.

pred audit-one i:gref, o:list gref.
audit-one G [] :- prim G _, !.
audit-one (const C) Callees :- lookup (const C) _, coq.env.const C (some _) _, !,
  new_safe S, (callee-safe S => timecheck (const C)), open_safe S Callees.
audit-one G [] :- lookup G _, !.
audit-one G _ :- err "E_AUDIT" {calc ("TimeAudit: " ^ {gstr G} ^
  " is reachable from the roots and has neither a time function nor a TimePrim cost")}.
}}.

Elpi Export TimeAudit.

(** [TimePrim c := (e)] declares the cost [e] of a built-in constant [c], whose type is the time
    type of [c]; [TimePrim c := n] declares a constant cost [n].  It is the only way to declare a
    cost by hand. *)

Elpi Command TimePrim.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate lp:{{
main [str S, str ":=", trm E] :- !, coq.locate S GR, check-untimed GR, prim-type GR TTy,
  (coq.elaborate-skeleton E TTy E2 ok, ! ;
   coq.error "TimePrim: the cost of" S "must have type" {coq.term->string TTy}),
  declare-prim GR E2.
main [str S, str ":=", int N] :- !, coq.locate S GR, check-untimed GR, prim-type GR TTy,
  nat-of N K, const-fun TTy K E, declare-prim GR E.
main _ :- coq.error "TimePrim: expected TimePrim c := (e) or TimePrim c := n".

pred prim-type i:gref, o:term.
prim-type GR TTy :- coq.env.typeof GR Ty, binder-shapes Ty Ss, tau Ty Ss TTy.

pred nat-of i:int, o:term.
nat-of 0 {{ 0 }} :- !.
nat-of N {{ S lp:K }} :- M is N - 1, nat-of M K.

pred const-fun i:term, i:term, o:term.
const-fun (prod N D B) K (fun N D R) :- !, pi x\ decl x N D => const-fun (B x) K (R x).
const-fun _ K K.

pred declare-prim i:gref, i:term.
declare-prim GR E :-
  @global! => coq.elpi.accumulate execution-site "argent.time.db" (clause _ _ (prim GR E)).
}}.

Elpi Export TimePrim.

(** [TimePrimTable] prints every cost declared with [TimePrim], sorted by the full name of its
    constant.  [TimePrimTable c ...] also fails unless the constants with a declared cost are
    exactly [c ...], so that a test can compare the table with the constants that extraction
    realises natively. *)

Elpi Command TimePrimTable.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate lp:{{
main Args :- std.findall (prim G_ E_) Facts, std.map Facts to-entry Entries,
  sort Entries Sorted, std.forall Sorted print-entry, expect-names Args Sorted.

kind entry type.
type ent string -> term -> entry.

pred to-entry i:prop, o:entry.
to-entry (prim GR E) (ent S E) :- gstr GR S.

pred print-entry i:entry.
print-entry (ent S E) :- coq.say S ":=" {tstr E}.

% Insertion sort by name.
pred sort i:list entry, o:list entry.
sort [] [].
sort [X|Xs] Ys :- sort Xs Zs, insert X Zs Ys.

pred insert i:entry, i:list entry, o:list entry.
insert X [] [X].
insert (ent S E) [ent T F|Ys] [ent S E, ent T F|Ys] :- S =< T, !.
insert X [Y|Ys] [Y|Zs] :- insert X Ys Zs.

pred expect-names i:list argument, i:list entry.
expect-names [] _ :- !.
expect-names Args Sorted :- std.map Args arg-name Names,
  std.map Names (n\ e\ e = ent n {{ 0 }}) Es, sort Es SortedEs,
  std.map SortedEs entry-name Want, std.map Sorted entry-name Have,
  (Want = Have, ! ;
   coq.error "TimePrimTable: the constants with a declared cost are" Have "and not" Want).

pred arg-name i:argument, o:string.
arg-name (str S) N :- !, coq.locate S GR, gstr GR N.
arg-name A _ :- coq.error "TimePrimTable: expected constant names, got" A.

pred entry-name i:entry, o:string.
entry-name (ent S _) S.
}}.

Elpi Export TimePrimTable.

(** [TimeUnfold c] makes the translation unfold [c] before translating its calls, so that, for
    example, an identity-monad [bind m (fun x => k)] is charged as [let x := m in k]. *)

Elpi Command TimeUnfold.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate lp:{{
main Args :- std.forall Args unfold-arg.

pred unfold-arg i:argument.
unfold-arg (str S) :- !, coq.locate S GR, unfold-ok GR,
  @global! => coq.elpi.accumulate execution-site "argent.time.db"
    (clause _ _ (unfold-const GR)).
unfold-arg A :- coq.error "TimeUnfold: expected constant names, got" A.

pred unfold-ok i:gref.
unfold-ok (const C) :- coq.env.const C (some _) _, !.
unfold-ok GR :- coq.error "TimeUnfold:" {gstr GR} "is not a transparent constant".
}}.

Elpi Export TimeUnfold.

(** [TimeBound L] registers the lemma [L : forall x, [P x ->] T_g x <= B x] for [time_pose].
    A lemma named [T_g_le] beside [T_g] is found without registration. *)

Elpi Command TimeBound.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate lp:{{
main Args :- std.forall Args bound-arg.

pred bound-arg i:argument.
bound-arg (str S) :- !, coq.locate S L, coq.env.typeof L Ty, bound-head Ty TG,
  @global! => coq.elpi.accumulate execution-site "argent.time.db" (clause _ _ (bound TG L)).
bound-arg A :- coq.error "TimeBound: expected lemma names, got" A.
}}.

Elpi Export TimeBound.

(** [TimeFunFails "E_CODE" f] succeeds when [TimeFun f] fails with the error code [E_CODE], and
    declares nothing.  It is the testing aid for rejections. *)

Elpi Command TimeFunFails.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate lp:{{
main [str Code, str S] :- !, coq.locate S GR, new_safe Safe,
  ((expect-error Safe => dry-run GR), ! ; true), open_safe Safe Codes, expect Code S Codes.
main _ :- coq.error "TimeFunFails: expected TimeFunFails \"E_CODE\" f".

pred dry-run i:gref.
dry-run GR :- check-code GR C, check-untimed GR, check-section C, check-placement GR,
  derive GR Rs, std.forall Rs (r\ sigma G T Ty\ r = res G T, check-typed G T Ty).

pred expect i:string, i:string, i:list string.
expect Code S [Code|_] :- !, coq.say "TimeFunFails:" S "is rejected with" Code.
expect Code S [Other|_] :- !,
  coq.error "TimeFunFails:" S "is rejected with" Other "instead of" Code.
expect Code S [] :- coq.error "TimeFunFails:" S "is accepted, expected" Code.
}}.

Elpi Export TimeFunFails.

(** * Unfolding time functions

    [unfold-once T R] unfolds an application of a time function by one step and refolds its
    recursive calls into the time function itself, then reduces beta and iota redexes.  The
    tactics [time_unfold] and [time_step] use it in place of [cbn], which never unfolds a time
    function. *)

Elpi File argent.time.unfold lp:{{

pred unfold-once i:term, o:term.
unfold-once (app [H|As]) R :- head-gref H (const C), const-body-at H C Bo, !,
  unfold-body H [] Bo As R.
unfold-once H R :- head-gref H (const C), const-body-at H C Bo, unfold-body H [] Bo [] R.

pred unfold-body i:term, i:list term, i:term, i:list term, o:term.
unfold-body H Ps (fun _ _ B) [A|As] R :- !, unfold-body H {std.append Ps [A]} (B A) As R.
unfold-body H Ps (fix _ I _ B) As R :- !, constructor-at I As, coq.mk-app H Ps HP,
  coq.mk-app (B HP) As R0, betaiota R0 R.
unfold-body H Ps (mfix J I Blk) As R :- !, constructor-at I As, member-values H Ps Blk Vs,
  block-body Blk Vs J BJ, coq.mk-app BJ As R0, betaiota R0 R.
unfold-body _ _ Bo As R :- coq.mk-app Bo As R0, betaiota R0 R.

% A recursive function unfolds by conversion only when its structural argument is a
% constructor.
pred constructor-at i:int, i:list term.
constructor-at I As :- std.length As N, I < N, std.nth I As A, coq.reduction.lazy.whd A W,
  constructor-head W.

pred constructor-head i:term.
constructor-head (global (indc _)).
constructor-head (pglobal (indc _) _).
constructor-head (app [H|_]) :- constructor-head H.

pred betaiota i:term, o:term.
betaiota T R :- @redflags! coq.redflags.betaiotazeta => coq.reduction.lazy.norm T R.

% The members of a mutual time function, each refolded to its sibling constant when there is
% one, or else kept as the closed fix term.
pred member-values i:term, i:list term, i:mfix-block, o:list term.
member-values H Ps Blk Vs :- block-names Blk Ns Rs, head-gref H GR, coq.gref->path GR P,
  member-values-from P Ps Blk 0 Ns Rs Vs.

pred member-values-from i:list string, i:list term, i:mfix-block, i:int, i:list name,
  i:list int, o:list term.
member-values-from _ _ _ _ [] [] [] :- !.
member-values-from P Ps Blk K [N|Ns] [R|Rs] [V|Vs] :-
  member-value P Ps Blk K N R V, K1 is K + 1, member-values-from P Ps Blk K1 Ns Rs Vs.

pred member-value i:list string, i:list term, i:mfix-block, i:int, i:name, i:int, o:term.
member-value P Ps _ _ N _ V :- coq.name->id N Id, std.append P [Id] L,
  std.string.concat "." L S, coq.locate-all S Locs, std.mem Locs (loc-gref G),
  coq.gref->path G P, !, coq.env.global G GT, coq.mk-app GT Ps V.
member-value _ _ Blk K _ R (mfix K R Blk).

pred block-body i:mfix-block, i:list term, i:int, o:term.
block-body (mfix-ty _ _ _ B) [V|Vs] J R :- !, block-body (B V) Vs J R.
block-body (mfix-bo Bs) [] J R :- std.nth J Bs R.

% [unfold-heads Gs T R]: unfold by one step every application in T of a constant in Gs.
pred unfold-heads i:list gref, i:term, o:term.
unfold-heads Gs T R :-
  ((pi h xs r\ copy (app [h|xs]) r :- head-gref h G, std.mem! Gs G,
     unfold-once (app [h|xs]) r, !) =>
   (pi h r\ copy h r :- head-gref h G, std.mem! Gs G, unfold-once h r, !) => copy T R).

}}.

(** Replace the goal by the convertible type [t]. *)
Ltac time_change t := change t.

Elpi Tactic time_unfold.
Elpi Accumulate Db argent.time.db.
Elpi Accumulate File argent.time.lib.
Elpi Accumulate File argent.time.unfold.
Elpi Accumulate lp:{{
pred arg-gref i:argument, o:gref.
arg-gref (trm T) G :- head-gref T G, !.
arg-gref A _ :- coq.ltac.fail _ "time_unfold: expected time functions, got" A.

solve (goal _ _ Ty _ Args as G) GL :- std.map Args arg-gref Gs,
  unfold-heads Gs Ty Ty2, coq.ltac.call "time_change" [trm Ty2] G GL.
}}.

(** Unfold by one step every application of the time function [t] in the goal whose
    structural argument is a constructor.  A time function never unfolds under [cbn] or
    [simpl]. *)
Tactic Notation "time_unfold" constr(t) := elpi time_unfold ltac_term:(t).
