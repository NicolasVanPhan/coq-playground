
Require Import Mycrush.
Require Import Bool Arith List.
Require Import Eqdep List Lia.
Set Implicit Arguments.

(* ================================================================================ *)
(** * 6 - Subset Types and Variations *)

(* ================================================================================ *)
(** * 6.1 - Introducing Subset Types *)

(* ================================================================================ *)
(** **            Q: Define [pred] and [pred_strong], asking for a proof of [n > 0] *)

Print pred.

Definition mypred (n : nat) : nat :=
  match n with
  | O => n
  | S n' => n'
  end.

Lemma zgtz : 0 > 0 -> False.
  crush.
Qed.

Definition mypred_strong1 (n : nat) : n > 0 -> nat :=
  match n with
  | O => (fun pf => (match zgtz pf with end))
  | S n' => (fun _ => n')
  end.

(* ================================================================================ *)
(** **            Q: Run [pred_strong] with [2] on the spot. *)

Lemma two_gt0 : 2 > 0.
crush. Qed.

Eval compute in mypred_strong1 two_gt0.

(* ================================================================================ *)
(** **            Q: What if you introduce [n > 0] early, next to [n] ? *)

(** We must use [return] annotation to help Rocq understand
    that n > 0 becomes 0 > 0 in the first case.

    However, annotation cannot bind :
    - the discriminee
    - with the type of a variable _already_ in scope
      (which is the case if [pf] is declared early)

    So we must introduce [pf] after the match-cases
    *)

Definition mypred_strong1' (n : nat) : n > 0 -> nat :=
  match n return n > 0 -> nat with
  | 0 => (fun pf : 0 > 0 => (match zgtz pf with end))
  | S n' => (fun _ => (n'))
  end.

(* ================================================================================ *)
(** **            Q: Re-implement [pred_v2] with subset types ? *)

Print sig.
Locate "{ _ : _ |  _ }".

Definition mypred_strong2 (s : {n : nat | n > 0}) : nat :=
  match s with
  | exist _ O pf => match zgtz pf with end
  | exist _ (S n') _ => n'
  end.

(* ================================================================================ *)
(** **            Q: Why is the extracted Ocaml code with subset types ? *)

(**
  Subset type is :
  - argument
  - proof about it

  The proof being erased, only 1 thing remains, the actual argument.
  Now, without the proof, [sig] has :
  - 1 constructor [exist]
  - with 1 argument [n] (and not two since [P] is out)

  Since inductive types of 1 ctor with 1 argument are useless,
  they don't bring more information than the argument itself,
  there's an optimization pass to erase them.

  That's why the resulting ocaml code is exactly the same as before.
*)

(* ================================================================================ *)
(** **            Q: Now [v3] - embed the proof that [n'] is the pred of [n] in the result type *)

Definition mypred_strong3 (s : {n : nat | n > 0}) : {n' : nat | S n' = proj1_sig s } :=
  match s with
  | exist _ O pf => match zgtz pf with end
  | exist _ ((S n') as n) _ => (exist _ n' (eq_refl (S n')))
  end.

Eval compute in mypred_strong3 (exist _ 2 two_gt0).

(* ================================================================================ *)
(** **            Q: Now [v4] - Shorter version using tactic style *)

Definition mypred_strong4' : forall n, n > 0 -> {m : nat | n = S m}.
  refine (fun (n : nat) (pf : n > 0) =>
  _
  ).
  destruct n.
  -  exfalso. apply zgtz. assumption.
  - exists n. reflexivity.
Defined.

Definition mypred_strong4'' : forall n, n > 0 -> {m : nat | n = S m}.
  refine (fun (n : nat) =>
    match n with
    | O => fun Hzgtz => False_rec _ (zgtz Hzgtz)
    | S n' => fun _ => exist _ n' (eq_refl (S n'))
    end
  ).
Defined.

Definition mypred_strong4''' : forall n, n > 0 -> {m : nat | n = S m}.
  refine (fun (n : nat) =>
    match n with
    | O => _
    | S n' => fun _ => exist _ n' _
    end
  ); crush.
Defined.

(* ================================================================================ *)
(** **            Q: Finally [v5] - Haskell style definition of [pred] *)

Notation "[ w ]" := (exist _ w _).

Definition mypred_final : forall n, n > 0 -> {m : nat | n = S m}.
  refine (fun (n : nat) =>
    match n with
    | O => _
    | S n' => fun _ => [n'] 
    end
  ); crush.
Defined.

Eval compute in (mypred_final two_gt0).


(* ================================================================================ *)
(** * 6.2 - Decidable Proposition Types *)

