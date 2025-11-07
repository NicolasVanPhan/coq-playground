
Require Import Bool List.
Set Implicit Arguments.
Set Asymmetric Patterns.

(** Goal: Practice pattern matching and recursion on inductive types.

Tasks:

- Define [add : nat -> nat -> nat]
- Define [mult : nat -> nat -> nat]
- Define [exp : nat -> nat -> nat] (exponentiation)

Stretch: Prove simple properties like:

- [thm1 : add n 0 = n]
- [thm2 : add 0 n = n]
- [thm3 : add n (S m) = S (add n m)]
- [thm4 : add n m = add m n] (commutativity of addition)
*)

Module Mynat.

Inductive mynat : Set :=
| O : mynat
| S : mynat -> mynat
.

Fixpoint add (n m : mynat) : mynat :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

(** Now let's prove some basics on additions  *)

Theorem thm1 : forall n : mynat, add n O = n.
Proof.
  induction n.
  - reflexivity.
  - simpl. rewrite IHn. reflexivity.
Qed.

Theorem thm2 : forall n : mynat, add O n = n.
Proof.
  induction n.
  - constructor.
  - simpl. reflexivity.
Qed.

Lemma thm3 : forall n m : mynat, add n (S m) = S (add n m).
Proof.
  induction n.
  - simpl. reflexivity.
  - intro m. simpl. rewrite IHn. reflexivity.
Qed.

Theorem thm4 : forall n m : mynat, add n m = add m n.
Proof.
  induction n.
  - (* Base case *)
    intro m. simpl. rewrite (thm1 m). reflexivity.
  - (* Inductive case *)
    intro m.
    simpl.
    rewrite -> thm3.
    rewrite IHn.
    reflexivity.
Qed.

(** My first intuitiion for mult is :

<<
  4 * 3 = 4 + 4 + 4
        = 4 + (4 * 2)
        = 4 + (4 + (4 * 1))
        = 4 + (4 + (4 + (4 * 0)))
        = 4 + (4 + (4 + 0))
        = 4 + 4 + 4 + 0
        = 4 + 4 + 4
>>

  The recursive pattern here is popping out a '4' and decrement the multiplier.
  [n * m = n + (n * (m-1))]
*)

Fixpoint mult_v1 (n m : mynat) : mynat :=
  match m with
  | O => O
  | S m' => add n (mult_v1 n m')
  end.

End Mynat.

(** It's not tail-recursive though
    Later we'll try to define a tail-recursive variant,
    and prove it equivalent to that one.
    For now let's just reason on that non-tail-recursive v1.
*)


(** Thoughts : What about an inductive definition of add ?

Something like :
*)

Inductive add : nat -> nat -> nat -> Prop :=
| Add_0 : add 0 0 0
| Add_S (n m p : nat) (IH : add n m p) : add (S n) m (S p)
| Add_C (n m p : nat) (IH : add n m p) : add m n p
.
