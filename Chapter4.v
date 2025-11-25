
Require Import Mycrush.
Require Import Bool Arith List.
Require Import Eqdep List Lia.
Set Implicit Arguments.

(* ================================================================================ *)
(** * 4.0 - Inductive Predicates *)

(* -------------------------------------------------------------------------------- *)
(** **           Q: Recall definition of [unit] and [True], and fundamental difference ? *)
Inductive my_unit : Set := my_tt : my_unit.
Inductive my_True : Prop := my_I : my_True.

Print my_unit.
Print unit.
Print my_True.
Print True.

(**
The differneces are :
- name (my_unit vs my_True), detail
- constructor name (tt vs I), detail
- Kind : Set vs Prop, that is the main difference.
*)

(* -------------------------------------------------------------------------------- *)
(** **           Q: Why not merging the two into 1 single type ? *)
(**

- Main argument : Proof irrelevance
  All functions [P -> Q] are not created equal, but all proof of proposition [P -> Q] are.
- Plus some other arguments on compilation efficiency
*)

(* -------------------------------------------------------------------------------- *)
(** **           Q: Goal of this chapter ? *)
(**
See how to define predicates with inductive definitions.
*)

(* ================================================================================ *)
(** * 4.1 - Propositional Logic *)

Section Propositional.
  Variables P Q R : Prop.

  Theorem ex_falso_example : False -> 2 + 2 = 5.
  Proof.
    intro HF. exfalso. apply HF.
  Qed.

  (* -------------------------------------------------------------------------------- *)
  (** **           Q: How to avoid the boilerplate of dealing with and/or/not ?
  e.g. Prove [P \/ Q -> Q \/ P] without manual use of [left], [right], etc.
  *)

  (** [tauto] to the rescue ! Complete decision procedure for constructive propositional logic. *)

  Theorem pq_qp : P \/ Q -> Q \/ P.
  Proof. tauto. Qed.

  (* -------------------------------------------------------------------------------- *)
  (** **           Q: What if [tauto] fails because of some missing hypothesis ? *)

  (** Use [intuition] instead, it will leave us the remaining bits to prove.
  *)

  Theorem arith_common : forall l1 l2 : list nat,
    length l1 = length l2 \/ length l1 + length l2 = 6
    -> length (l1 ++ l2) = 6 \/ length l1 = length l2.
  Proof.
    intuition.
    rewrite length_app.
    intuition.
  Qed.

  (* -------------------------------------------------------------------------------- *)
  (** **           Q: Common clean way to rewrite the above proof ? *)

  (**
  The [intuition] tactic could work if it knew about [length_app] for rewrites.

  First give the rewrite hint, then call [crush], which calls [intuition] actually.
  *)

  Theorem arith_common_v2 : forall l1 l2 : list nat,
    length l1 = length l2 \/ length l1 + length l2 = 6
    -> length (l1 ++ l2) = 6 \/ length l1 = length l2.
  Proof.
    Hint Rewrite length_app.
    crush.
  Qed.

End Propositional.


(* ================================================================================ *)
(** * 4.5 - Recursive Predicates *)

(* -------------------------------------------------------------------------------- *)
(** **           Q: Define [even] and manually prove [even 0], [even 4] *)

Inductive even : nat -> Prop :=
| even_O : even 0
| even_SS : forall n : nat, even n -> even (S (S n))
.

Theorem even_0 : even 0.
Proof.
  constructor.
Qed.

Theorem even_4 : even 4.
Proof.
  constructor; constructor; constructor.
Qed.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Automate [even 4] *)

(**
When the problem is just about applying constructors, [auto] can do the job easily.
*)

Hint Constructors even.
Theorem even_4' : even 4.
Proof.
  auto.
Qed.

  (* -------------------------------------------------------------------------------- *)
(** **           Q: prove [~even 1] *)

Theorem not_even_1 : ~ even 1.
Proof.
  intro H.
  inversion H.
Qed.

Theorem not_even_1' : ~ even 1.
Proof.
  inversion 1.
Qed.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Prove [~even 3]. *)
Theorem not_even_3 : ~ even 3.
Proof.
  inversion 1.
  inversion H1.
Qed.

(* TODO : How to help [inversion] finish the job ? *)

(* -------------------------------------------------------------------------------- *)
(** **           Q: Prove [~even_plus]. Why not trivial ? *)

(**
It's not trivial because the inductive case tries [P n -> P (S n)]
While we'd prefer a pattern like [P n -> P (S (S n))]
*)

Theorem even_plus : forall n m : nat, even n -> even m -> even (n + m).
Proof.
  induction n.
  - simpl. intros. assumption.
  - intros. simpl.
Abort.

Theorem even_plus_2 : forall n m : nat, even n -> even m -> even (n + m).
Proof.
  intros.
  induction H.
  - simpl. assumption.
  - simpl. constructor. assumption. 
Abort.

(**
Or better, since [H] appears as the first hypothesis, we can do : [induction 1].
*)

Theorem even_plus_final : forall n m : nat, even n -> even m -> even (n + m).
Proof.
  induction 1; crush.
Abort.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Lesson learned ? Proving [even_plus]. *)

(** Instead of [induction n], use [induction (even n)].
    It's called *rule induction* and very handy.

    Instead of pattern-matching over how [n] was constructed.
    (with induction step linkin [n] with [n+1], not interesting.)
    We pattern-match over how [even n] was constructed.
    (with induction step linking [n] with [n+2], more fruitful.)
*)

(* -------------------------------------------------------------------------------- *)
(** **           Q: Now prove [~even (2*n + 1)] *)

(**
We could try rule induction like before.
But with recursive predicates, [induction] is weird sometimes.
If we try, we get stuck with empty hypotheses.
It's related to how [induction] replaces [S (n + n)] with a fresh variable internally.
*)

Theorem even_contra : forall n : nat, even (S (n + n)) -> False.
Proof.
  intros.
  induction H.
Abort. 

Lemma even_contra_1 : forall n : nat, even n -> forall x, n = S (x + x) -> False.
Proof.
  intros.
  generalize dependent x. (* You're stuck without it !*)
  induction H; crush.
  destruct n; destruct x; crush. 
  rewrite Nat.add_succ_r in *.
  rewrite H0 in IHeven.
  apply (IHeven x).
  reflexivity.
Qed.

(**
We get stuck without [generalize dependent x],
but once we generalize [x], the rest is just about rewrites and applies.
The two main parts are :
- rule induction
- removing the cases where [n] or [x] are zero (hence the [destruct]s)
- Rewrite [_ + S _]

Hence a simplified version of our lemma below

*)

Lemma even_contra_lemma : forall n : nat, even n -> forall x, n = S (x + x) -> False.
Proof.
  Hint Rewrite Nat.add_succ_r.
  induction 1; crush.
  destruct n; destruct x; crush. 
Qed.

(**
Next trick : instead of using introduced variable, which is unstable and error-prome
better pattern-match on the goal
*)

Lemma even_contra_lemma_final : forall n : nat, even n -> forall x, n = S (x + x) -> False.
Proof.
  Hint Rewrite <- Nat.add_succ_r.
  induction 1; crush.
  match goal with
  | [ H : S ?N = ?X + ?X |- _ ] => destruct N; destruct X
  end; crush.
Qed.

(**
Now for the final theorem :
*)

Lemma even_contra: forall n', even n' -> forall n, n' = S (n + n) -> False.
Proof.
  intros.
  apply (even_contra_lemma_final H n).
  auto.
Qed.

(**
Or more simply, use [eapply] instead of [apply] so you let the prover
find the right arguemnts for you.
*)

Lemma even_contra_final: forall n', even n' -> forall n, n' = S (n + n) -> False.
Proof.
  intros. eapply even_contra_lemma_final; eauto.
Qed.


(* -------------------------------------------------------------------------------- *)
(** **           Q: Lesson learned ? Proving [~even (2n+1)] *)

(**
Several tips :
- Rule induction is still a good advice.
- When [induction] is lost, prove backwards through lemmas
  mentioning the expressions of interest
- Search rewrites with [SearchRewrite]
- Help [crush] with the appropriate [Hint Rewrite xxx]
- When [apply] doesn't find the instances, try [eapply] instead.

*)


(* -------------------------------------------------------------------------------- *)
(** **           Q: What problem occurs when introducing variables to soon ? *)

(**
Proof gets stuck because of of free variable that should be bound.
e.g.

[[
forall n x: nat, even n -> n = S (x + x) -> False.
]]
Introducing [x] too soon will specialize it before doing the induction.
So we'll want to [generalize] it before calling [induction].
We'll have a stronger goal but a stronger inductive hypothesis,
which in genenral works better.
*)

Lemma even_contra_too_soon : forall n x: nat, even n -> n = S (x + x) -> False.
Proof.
  Hint Rewrite <- Nat.add_succ_r.
  intros.
  generalize dependent x.
  induction H; crush.
  match goal with
  | [ H : S ?N = ?X + ?X |- _ ] => destruct N; destruct X
  end; crush.
Qed.

