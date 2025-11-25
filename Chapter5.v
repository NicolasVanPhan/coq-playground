
Require Import Mycrush.
Require Import Bool Arith List.
Require Import Eqdep List Lia.
Set Implicit Arguments.

(* ================================================================================ *)
(** * 5 - Infinite Data and Proofs *)


(* -------------------------------------------------------------------------------- *)
(** **           Q: What will go wrong if we can define non-terminating functions ? *)

(**
- You could define a proof of [False], breaking the logic.
- Tactics evaluating functions, like [reflexivity], could hang forever.
- Rocq couldn't determine whether the functions define would terminate
  (as it would be equivalent to the Halting problem, undecidable)
*)

(** An example of proof of false we could build in that case : *)
Fail Fixpoint bad (u : unit) : False := bad u.

(* -------------------------------------------------------------------------------- *)
(** **           Q: So how can we play with infinite lazy structures in Rocq ? *)

(** With *coinductive types*, the subject of this chapter. *)

(* ================================================================================ *)
(** * 5.1 - Computing with Infinite Data *)

Section Stream.
  Variable A : Type.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Define streams (infinite lists). *)

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream
  .
End Stream.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Define the stream of zeroes. *)

CoFixpoint zeroes : stream nat := Cons 0 zeroes.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Define the stream of alternating true/false. *)

(** A first tentative : *)

CoFixpoint alt_true_false (b : bool) : stream bool := 
  Cons b (alt_true_false (negb b)).

(** The problem is the input boolean [b],
    the idea of an infinite alternating list shouldn't ask for a boolean value.
    It means [alt_true_false true] and [alt_true_false false] should be the same object.
    So the boolean shouldn't be required at all.

    Below definition solves this problem. *)

CoFixpoint true_false : stream bool := Cons true false_true
with       false_true : stream bool := Cons false true_false.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Write an [approx] function to convert streams to lists. *)


Fixpoint approx (A : Type) (s : stream A) (n : nat) : list A :=
  match n with
  | O => nil
  | S n' => (
      match s with
      | Cons h t => h :: (approx t n')
      end
  )
  end.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Sanity-check your definitions with some examples. *)

Eval simpl in (approx zeroes 10).
(*
     = 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: nil
     : list nat
*)

Eval simpl in (approx true_false 5).
Eval simpl in (approx false_true 5).
Eval simpl in (approx false_true 1).
Eval simpl in (approx false_true 0).


(* -------------------------------------------------------------------------------- *)
(** **           Q: Compare [Fixpoint] and [CoFixpoint]. Restrictions of both ? *)

(**
[Fixpoint] _consumes_ values of inductive types,
and has restriction on its argument (which must decrease).
[CoFixpoint] _produces_ values of coinductive types,
and has restrictions on its return value (which must increase).

Below are dual example of forbidden looping fixpoint and cofixpoint.
- [loop] is forbidden because its argument doesn't decrease.
- [coloop] is forbidden because its return value doesn't increase.

*)

Fail Fixpoint loop (u : unit) : unit := loop u.

Fail CoFixpoint coloop (s : stream unit) : stream unit := coloop s.

(** If [coloop] weren't guarded, our [approx] function could have run forever. *)

(* -------------------------------------------------------------------------------- *)
(** **           Q: Write a [map] function over [stream]s.  *)

Section stream_map.
  Variables A B : Type.

  CoFixpoint stream_map (f : A -> B) (s : stream A) : stream B :=
    match s with
    | Cons h t => Cons (f h) (stream_map f t)
    end.
End stream_map.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Example of classic function that does have its dual ? *)

(** The [filter] function can't have a cofixpoint dual.
    Indeed, if the filter rejects every element in the stream,
    it cannot satisfy the guardedness condition.
    Running [filter] with such an all-rejecting filter will hang forever. *)

(* -------------------------------------------------------------------------------- *)
(** **           Q: More subtle example violating guardedness condition ? *)

Section interleave.
  Variables A : Type.

  CoFixpoint interleave (s1 s2 : stream A) : stream A :=
    match s1, s2 with
    | Cons h1 t1, Cons h2 t2 => Cons h1 (Cons h2 (interleave t1 t2))
    end.
End interleave.

Section map'.
  Variables A B : Type.
  Variables f : A -> B.

  Fail CoFixpoint map' (s : stream A) : stream B :=
    match s with
    | Cons h t => interleave (Cons (f h) (map' t)) (Cons (f h) (map' t))
    end.
End map'.

(** Rocq will reject definitions when it can't ensure the _productivity_ condition. *)

Definition tail' (s : stream nat) : stream nat :=
  match s with
  | Cons _ t => t
  end.

Fail CoFixpoint bad : stream nat := tail' (Cons 0 bad).

(** Here the return value doesn't grow, because the additional constructor
    is then removed by the sneaky [tail'] function, so the net progress is zero.
    In that case, we would have just defined an infinite loop, breaking Rocq.

    To ensure the return value grows,  Rocq not only demands a constructor,
    but demands that everything touching the return value is harmless (not shrinking).
    So functions are forbidden. Only constructors, and [fun], [match] blocs.

    > No shrinking stuffs !

    *)


(* ================================================================================ *)
(** * 5.2 - Infinite Proofs *)

(* -------------------------------------------------------------------------------- *)
(** **           Q: Give example of 2 equal streams, and prove them equal. *)

CoFixpoint all_ones_a : stream nat := Cons 1 all_ones_a.
Definition all_ones_b : stream nat := stream_map S zeroes.

Section stream_eq.
  Variables A : Type.

  CoInductive stream_eq : stream A -> stream A -> Prop := 
  | Stream_Eq : forall h t1 t2, stream_eq t1 t2 -> stream_eq (Cons h t1) (Cons h t2)
  .
End stream_eq.

Theorem stream_a_eq_b_try1 : stream_eq all_ones_a all_ones_b.
Proof.
  cofix stream_eq.
  assumption.
  Fail Guarded.
Abort.

Definition frob A (s : stream A) : stream A :=
match s with
| Cons h t => Cons h t
end.

Lemma frob_eq : forall A, forall (s : stream A), frob s = s.
Proof. intros. destruct s. simpl. reflexivity. Qed.
  
Theorem stream_a_eq_b_try2 : stream_eq all_ones_a all_ones_b.
Proof.
  cofix stream_eq.
  rewrite <- (frob_eq all_ones_a).
  rewrite <- (frob_eq all_ones_b).
  unfold frob in *.
  simpl.
  constructor.
  assumption.
  Guarded.
Qed.

(* -------------------------------------------------------------------------------- *)
(** **           Q: APARTE : Print and explain the generated proof term [stream_a_eq_b_try2] *)



(** Destructuring the generated proof term : 

<<
Print stream_a_eq_b_try2.

Check eq_ind.
(A : Type)         1. A            
(x : A)            2. x            
(P : A -> Prop),   3. P            
P x ->             4. P x          
forall y : A,      5. y            
x = y              6. x = y        
-> P y             result : P y    


Definition stream_a_eq_b_try2' :=
  cofix stream_eq : stream_eq all_ones_a all_ones_b :=
    eq_ind
--- 2. x ---------------------- i.e.  big_a ------------------------------------
      (frob all_ones_a)   
--- 3. P ---------------------- i.e.  s= b -------------------------------------
      (fun s : stream nat => cpdt_notes.stream_eq s all_ones_b) 
--- 4. P x -------------------- i.e.  big_a  s=  b -----------------------------
      (eq_ind
-------- 2. x ------ i.e. big_b  -----------------------------------------------
          (frob all_ones_b)
-------- 3. P ------ i.e. s= big_a ---------------------------------------------
          (fun s : stream nat => cpdt_notes.stream_eq (frob all_ones_a) s)
-------- 4. P x ---- i.e. big_b s= big_a ---------------------------------------
          (
            (
              Stream_Eq 1 stream_eq
              
              : cpdt_notes.stream_eq
                 ( match all_ones_a with | Cons h t => Cons h t end )
                 ( match all_ones_b with | Cons h t => Cons h t end )
              : cpdt_notes.stream_eq (frob all_ones_a) (frob all_ones_b)
            )
        
---------- 5. y ----- i.e.  b --------------------------------------------------
        all_ones_b
---------- 6. x = y - i.e. big_b = b -------------------------------------------
        (frob_eq all_ones_b)
      )
-------- res  : P y   i.e.  b s= big_a  ----------------------------------------

--- 5. y ----------------------- i.e.  a ---------------------------------------
      all_ones_a  
--- 6. x == y ------------------ i.e.  big_a = a -------------------------------
      (frob_eq all_ones_a)
--- res ------------------------ i.e   a s= b ----------------------------------
  : stream_eq all_ones_a all_ones_b
>>

*)

(* -------------------------------------------------------------------------------- *)
(** **           Q: Proof v2 : Define a coinduction principle
                    to prove stream equality, and use it. *)

(** Now let's do better.
Instad of the boilerplate of magic but painful [frob],
let's try to arrive at a [induction x; crush.] style of proof.

And to do so, we'll start by defining a coinductive principle for stream eq.

*)

Definition hd A (s : stream A) : A :=
match s with
| Cons h _ => h
end.

Definition tl A (s : stream A) : stream A :=
match s with
| Cons _ t => t
end.

Section stream_eq_coind.
  Variables A : Type.

  (** Define a relation [R] that will represent our property (here stream equality) *)
  Variables R : stream A -> stream A -> Prop.

  (** Define all that must be true for the property to hold (here equality of heads,
      and passing-on the R-ness to the tail) *)
  Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> hd s1 = hd s2.
  Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tl s1) (tl s2).

  (** Now prove that this [R] relation satisfies stream equality *)
  Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> stream_eq s1 s2.
  Proof.
    cofix stream_eq_coind.
    intros.

    (** Nice trick to get equality of both heads (a = a0) *)
    destruct s1, s2. generalize (Cons_case_hd H).
    intro Heq. simpl in Heq. rewrite Heq in *.
    (** Moving 1 coinductive step forward *)
    constructor.
    (** Now we've move forward one step, we can apply the co-inductive hypothesis. *)
    apply stream_eq_coind.
    apply (Cons_case_tl H).

    Guarded.
  Qed.

  Print stream_eq_coind.
End stream_eq_coind.

(** Now any predicates that satisfies
    [Cons_case_hd] and [Cons_case_tl] will do the job.  *)

Theorem stream_a_eq_b_try3 : stream_eq all_ones_a all_ones_b.
Proof.
  apply (stream_eq_coind(
    fun s1 s2 => s1 = all_ones_a /\ s2 = all_ones_b)); crush.
Qed. 

(* -------------------------------------------------------------------------------- *)
(** **           Q: APARTE : Illustrate the 'copy/paste' from [stream_eq] to [stream_eq_coind]. *)

(**

It was not clear to me how the hypotheses of the coinductive principle
derive immediately from the arguments of the constructor in the coinductive type definition.
i.e. you take the arguments of [Stream_Eq] and you get your hypotheses for [stream_eq_coind].

It was not clear because [stream_eq] talks in [s1] and [s2], and cleverly uses a single [h]
to force equality of heads,

while [stream_eq_coind] talks in [h1]/[t1] and [h2]/[t2].

But we can remove this clever compactness and rewrite [stream_eq] as below.
*)

Section stream_eq_raw.
  Variables A : Type.
  CoInductive stream_eq_raw : stream A -> stream A -> Prop := 
(** First way (and only) to build a proof of [stream_eq s1 s2] *)
  | Stream_Eq' : forall s1 s2,         
(** Precond 1 : equality of heads *)
      (hd s1) = (hd s2) ->             
(** Precond 2 : equality of tails *)
      stream_eq_raw (tl s1) (tl s2) -> 
(** The result : equality of streams, our [stream_eq s1 s2]  *)
      stream_eq_raw s1 s2              
  .


(** Now for the coind principle,
    the hypotheses are exactly the preconds above. *)

  Variables R : stream A -> stream A -> Prop.

(** Precond 1 : equality of heads *)
  Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> hd s1 = hd s2.       (* Precond 1 : equality of heads *)
(** Precond 2 : equality of tails *)
  Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tl s1) (tl s2).   (* Precond 2 : equality of tails *)

(** The result : equality of streams, our [stream_eq s1 s2]  *)
  Theorem stream_eq_coind_raw : forall s1 s2, R s1 s2 -> stream_eq s1 s2.     (* Both precond -> stream equality *)
  Abort.

End stream_eq_raw.



(* -------------------------------------------------------------------------------- *)
(** **           Q: Proof v3 : How to prove equality without defining any [R] ? *)

(** Better, but we still have to define a clever [R], this is annoying *)

Section stream_eq_loop.
  Variables A : Type.
  Variables s1 s2 : stream A.

  Hypothesis Cons_case_hd : hd s1 = hd s2. 
  Hypothesis loop1 : tl s1 = s1.
  Hypothesis loop2 : tl s2 = s2.

  Theorem stream_eq_loop : stream_eq s1 s2.
    apply (stream_eq_coind (
      fun s1' s2' => s1' = s1 /\ s2' = s2
    )); crush.
  Qed.
End stream_eq_loop.

Theorem stream_a_eq_b_try4 : stream_eq all_ones_a all_ones_b.
Proof.
  apply stream_eq_loop; crush.
Qed.


(* -------------------------------------------------------------------------------- *)
(** **           Q: Factorials : Define the stream of factorials
                    (naive and iterative variants). *)

Print fact.
 
(**
Let's build the stream of all factorials.
The simplest and naive way is to call [fact] on all elements.
*)
CoFixpoint fact_slow_aux (n : nat) : stream nat := Cons (fact n) (fact_slow_aux (S n)).
Definition fact_slow := fact_slow_aux 1.

(** Now a clever implementation with an accumulator *)

CoFixpoint fact_iter_aux (n acc : nat) :=
  Cons (acc) (fact_iter_aux (S n) (n * acc)).
Definition fact_iter := fact_iter_aux 2 1.

Eval simpl in approx fact_slow 5.
Eval simpl in approx fact_iter 5.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Factorials v1 : Prove them equal *)

(** Some magic in the book not explained on purpose yet. *)
Lemma fact_def : forall x n,
fact_iter_aux x (fact n * S n) = fact_iter_aux x (fact (S n)).
simpl; intros; f_equal; ring.
Qed.
Hint Resolve fact_def.

Check stream_eq_coind.

Lemma fact_eq' : forall n,
  stream_eq (fact_iter_aux (S n) (fact n)) (fact_slow_aux n).
Proof.
  pose (R := (fun s1 s2 => exists n,
    s1 = (fact_iter_aux (S n) (fact n)) /\
    s2 = (fact_slow_aux n)
  )).
  intro; apply (stream_eq_coind R); unfold R in *; crush; eauto.
Qed.
  
Theorem fact_eq : stream_eq fact_iter fact_slow.
Proof. apply fact_eq'. Qed.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Factorials v2 : Simpler proof of lemma
                    through [stream_eq_loop] trick. *)

Section stream_eq_loop_onequant.
  Variables A B : Type.
  Variables f1 f2 : A -> stream B.

  Hypothesis Coind_hd : forall x, hd (f1 x) = hd (f2 x).
  Hypothesis Coind_tl : forall x, exists y, tl (f1 x) = f1 y /\ tl (f2 x) = f2 y.

  Theorem stream_eq_loop_onequant : forall x, stream_eq (f1 x) (f2 x).
  Proof.
    intros.
    apply (stream_eq_coind (
      fun s1 s2 => exists y, s1 = (f1 y) /\ s2 = (f2 y)
    )); crush; eauto.
  Qed.
End stream_eq_loop_onequant.


Lemma fact_eq'' : forall n,
  stream_eq (fact_iter_aux (S n) (fact n)) (fact_slow_aux n).
Proof.
  apply stream_eq_loop_onequant; crush; eauto.
Qed. 


(* ================================================================================ *)
(** * 5.3 - Simple Modeling of non-terminating programs *)

(* -------------------------------------------------------------------------------- *)
(** **           Q: Define a little language with :
 
  The memory : 
  - [var] as [nat]
  - [vars] as a map from variables to values
  - [set] to assign a value to a variable
  
  The expressions :
  - constant
  - variable
  - addition

  (and an evaluation function)

  The commands :
  - assignment
  - sequence
  - while loop (let's say [cond : expr], and [false] means [eq 0])
*)



Definition var := nat.
Definition vars := var -> nat.

Definition set (vs : vars) (v : var) (n : nat) : vars :=
  fun v' => if Nat.eqb v' v then n else vs v.

(* Little imperative language *)

Inductive exp : Set :=
| E_Const : nat -> exp
| E_Var : var -> exp
| E_Plus : exp -> exp -> exp
.

Fixpoint evalExp (vs : vars) (e : exp) : nat :=
  match e with
  | E_Const n => n
  | E_Var v => vs v
  | E_Plus e1 e2 => (evalExp vs e1) + (evalExp vs e2)
  end.

Inductive cmd : Set :=
| C_Asgn : var -> exp -> cmd    (* variable assignment *)
| C_Seq : cmd -> cmd -> cmd     (* sequence operator *)
| C_While : exp -> cmd -> cmd  (* while (expr) { cmd } *)
.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Now, what object to define the evaluation of command, and why ? *)

(** Defining it as a function won't work because
    it could not terminate because of infinite [C_While] loops,
    and Rocq won't allow us to build such a non-terminating function.
    
    Below we try and it indeed fails,
    saying it can't determine a decreasing argument,
    which is normal because there can't be one.
*)

Fail Fixpoint evalCmd_fix (vs : vars) (c : cmd) : vars :=
  let self := evalCmd_fix in
  match c with
  | C_Asgn v e => set vs v (evalExp vs e)
  | C_Seq c1 c2 => (
    let vs' := self vs c1 in
    self vs' c2)
  | C_While cond body => (if Nat.eqb (evalExp vs cond) 0 then vs else (
    let vs' := self vs body in
    self vs' c))
  end.

(** Inductive definition won't capture non-terminating executions.
    So we go with the CoInductive definition.  *)
CoInductive evalCmd : vars -> cmd -> vars -> Prop :=
| EC_Assign : forall (vs : vars) (v : nat) (e : exp), 
    evalCmd vs (* *) (C_Asgn v e) (* *) (set vs v (evalExp vs e))
| EC_Seq : forall c1 c2 vs vs' vs'',
    evalCmd vs  c1 vs' ->
    evalCmd vs' c2 vs'' ->
    evalCmd vs (* *) (C_Seq c1 c2) (* *) vs''
| EC_WhileFalse : forall cond body vs,
    (evalExp vs cond) = 0 ->
    evalCmd vs (* *) (C_While cond body) (* *) vs
| EC_WhileTrue : forall cond body vs vs' vs'',
    (evalExp vs cond) <> 0
    -> evalCmd vs  (* *) body (* *) vs' 
    -> evalCmd vs' (* *) (C_While cond body) (* *) vs'' 
    -> evalCmd vs  (* *) (C_While cond body) (* *) vs''
.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Define a coinductive principle for the [evalCmd] relation.  *)

Section evalCmd_coind.

  Variables R : vars -> cmd -> vars -> Prop.

  Hypothesis HC_Asgn : forall vs vs' v e,
    R vs (C_Asgn v e) vs'
    -> vs' = (set vs v (evalExp vs e)).
  
  Hypothesis HC_Seq : forall c1 c2 vs vs',
    R vs (C_Seq c1 c2) vs'
    -> exists vs'', R vs c1 vs'' /\ R vs'' c2 vs'.
  
  Hypothesis HC_While : forall vs vs' cond body,
    R vs (C_While cond body) vs'
    -> (evalExp vs cond = 0 /\ vs = vs') (* While false case *)
    \/ (exists vs'', evalExp vs cond <> 0 /\ (R vs body vs'' /\ R vs'' (C_While cond body) vs' )).


    Theorem evalCmd_coind : forall vs vs' c, R vs c vs' -> evalCmd vs c vs'.
    Proof.
      cofix evalCmd_coind.
      intros; destruct c.
      - rewrite (HC_Asgn H). constructor.
      - destruct (HC_Seq H) as [? [? ?]]. econstructor; eauto.
      - destruct (HC_While H) as [ [? ?] | [? [? [? ?]] ] ];
        subst; econstructor; eauto.
    Qed. 

End evalCmd_coind.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Now write a simple optimizing pass replacing [0 + e] with [e].  *)

Fixpoint optExp (e : exp) : exp :=
  match e with
  | E_Const n => e
  | E_Var v  => e
  | E_Plus e1 e2 => (
    let e1' := optExp e1 in
    let e2' := optExp e2 in
    match e1' with
    | E_Const 0 => e2'
    | _ => E_Plus e1' e2'
    end
  )
  end.


Fixpoint optCmd (c : cmd) : cmd :=
  match c with
  | C_Asgn v e => C_Asgn v (optExp e)
  | C_Seq c1 c2 => C_Seq (optCmd c1) (optCmd c2)
  | C_While cond body => C_While (optExp cond) (optCmd body)
  end.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Prove [optExp] correct.  *)

Lemma optExp_correct_v1 : forall vs e, evalExp vs (optExp e) = evalExp vs e.
Proof.
  intros.
  induction e.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl.
    destruct (optExp e1).
    + destruct n.
      * rewrite <- IHe1. rewrite IHe2. simpl. reflexivity.
      * simpl.
        rewrite <- IHe1. rewrite <- IHe2. simpl. reflexivity.
    + rewrite <- IHe1. rewrite <- IHe2. simpl. reflexivity.
    + rewrite <- IHe1. rewrite <- IHe2. simpl. reflexivity.
Qed.

Lemma optExp_correct_v2 : forall vs e, evalExp vs (optExp e) = evalExp vs e.
Proof.
  induction e; crush.

  (match goal with 
  | [|- context[ match ?E with E_Const _ => _ | _ => _ end]] => destruct E
  end ); crush.

  (match goal with 
  | [|- context[ match ?E with O => _ | S _ => _ end]] => destruct E
  end ); crush.
Qed.

Lemma optExp_correct : forall vs e, evalExp vs (optExp e) = evalExp vs e.
Proof.
  induction e; crush.
  repeat (match goal with 
  | [|- context[ match ?E with E_Const _ => _ | _   => _ end]] => destruct E
  | [|- context[ match ?E with O         => _ | S _ => _ end]] => destruct E
  end; crush).
Qed.

Hint Rewrite optExp_correct.

(* -------------------------------------------------------------------------------- *)
(** **           Q: BONUS: Prove [optCmd] correct (left unexplained in the book).  *)

Ltac finisher :=
  match goal with
  | [H : evalCmd _ _ _ |- _] => (
    (inversion H; []) ||
    (inversion H; [|])
  ); subst
  end; crush; eauto 10.

Lemma optCmd_correct1 : forall vs1 vs2 c,
  evalCmd vs1 c vs2 -> evalCmd vs1 (optCmd c) vs2.
Proof.
  intros;
  apply (evalCmd_coind (fun vs1 c' vs2 => exists c,
    evalCmd vs1 c vs2 /\ c' = optCmd c
  )); eauto; crush;

  destruct x; simpl in *; try discriminate H2; try injection H2; intros; subst; finisher.
Qed.
  
Lemma optCmd_correct2 : forall vs1 vs2 c,
  evalCmd vs1 (optCmd c) vs2 -> evalCmd vs1 c vs2.
Proof.
  Check evalCmd_coind.
  intros. apply (evalCmd_coind (fun vs c vs' =>
    evalCmd vs (optCmd c) vs'
  )); eauto; crush; finisher.
Qed.
  
Theorem optCmd_correct : forall vs1 vs2 c,
  evalCmd vs1 (optCmd c) vs2 <-> evalCmd vs1 c vs2.
Proof.
  intuition; apply optCmd_correct1 || apply optCmd_correct2; assumption.
Qed.


Check 0.



