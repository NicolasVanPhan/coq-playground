
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

(* ================================================================================ *)
(** **            Q: Define [eq_nat_deciable : {n = m} + {n <> m} *)


Definition eq_nat_decidable_raw : forall n m : nat, {n = m} + {n <> m}.
  refine(
    fix f (n m : nat) :=
    match n, m with
    | O, O => left (eq_refl O)
    | S n', S m' => (match f n' m' with
      | left _ => left _
      | right _ => right _
      end
    )
    | _, _ => right _
    end);

    try (intro Hcontra; discriminate || congruence).

    try (match goal with
    | [ H : n' = m' |- _] => rewrite H
    end; reflexivity).

Defined.

Eval compute in eq_nat_decidable_raw 2 2.
Eval compute in eq_nat_decidable_raw 2 3.

(* ================================================================================ *)
(** **            Q: v2 with [Yes]/[No]/[Reduce] notation *)

Notation "'Yes'" := (left _ _).
Notation "'No'" := (right _ _).
Notation "'Reduce' x" := (if x then Yes else No) (at level 50).

Definition eq_nat_decidable_v2 : forall n m : nat, {n = m} + {n <> m}.
  refine(
    fix f (n m : nat) :=
    match n, m with
    | O, O => Yes
    | S n', S m' => Reduce (f n' m')
    | _, _ => No
    end)
    ; crush.
Defined.

Eval compute in eq_nat_decidable_v2 2 2.
Eval compute in eq_nat_decidable_v2 2 3.

(* ================================================================================ *)
(** **            Q: v3 in one line *)

Definition eq_nat_decidable_v3 : forall n m : nat, {n = m} + {n <> m}.
  decide equality.
Defined.

(* ================================================================================ *)
(** **            Q: Define [In_decidable] with and without Yes/No/Reduce notation. *)

Notation "x || y" := (if x then Yes else Reduce y).

Section In_dec.
    Variable A : Set.
    Variable A_eq_dec : forall x y : A, {x = y} + {x <> y}.

    Definition In_dec_raw : forall (x : A) l, {In x l} + {~(In x l)}.
      refine (
        fix f (x : A) (l : list A) :=
          match l with
          | nil => No
          | cons x' l' => (
              match A_eq_dec x x' with
(** Notation : [A_eq_dec x x'] *)
              | left Heq => left _
(** Notation : [||] *)
              | right Hneq => (
(** Notation : [Refine f x l'] *)
                  match f x l' with
                  | left _ => left _
                  | right _ => right _
                  end
              )
              end
          )
          end
      ); crush.
    Defined.

    Definition In_dec : forall (x : A) l, {In x l} + {~(In x l)}.
      refine (
        fix f (x : A) (l : list A) :=
          match l with
          | nil => No
          | cons x' l' => A_eq_dec x x' || f x l'
          end); crush.
    Defined.

End In_dec.

Eval compute in (In_dec_raw eq_nat_dec 2 (1 :: 2 :: nil)).
Eval compute in (In_dec_raw eq_nat_dec 3 (1 :: 2 :: nil)).
Eval compute in (In_dec_raw eq_nat_dec 2 (nil)).


(* ================================================================================ *)
(** * 6.3 - Partial Subset Types *)

(* ================================================================================ *)
(** **            Q: Define The [maybe] type *)

Inductive maybe (A : Set) (P : A -> Prop) : Set :=
| Unknown : maybe P
(** Alternative : [| Found (x : A) (H : P x) : maybe P] *)
| Found : forall x : A, P x -> maybe P
.

Notation "{{ x | P }}" := (maybe (fun x => P)).
Notation "??" := (Unknown _).
Notation "[| x |]" := (Found _ x _).

(* ================================================================================ *)
(** **            Q: v7 of [pred], using the [maybe] notation. *)

Definition pred_v7 : forall n : nat, {{ m | S m = n }}.
  refine (
    fun n =>
      match n with
      | O => ??
      | S n' => [| n' |]
      end
  ); trivial.
Defined.

Eval compute in (pred_v7 3).
Eval compute in (pred_v7 1).
Eval compute in (pred_v7 0).

(* ================================================================================ *)
(** **            Q: Why is the [maybe] type too loose for pred here ? *)

(** The below dummy implementation is valid, i.e. the function type
    allows such useless implementations. *)

Definition pred_dummy : forall n : nat, {{ m | S m = n}}.
  refine ( fun n => ?? ).
Defined.

(** For sure we want the type to enforce pred values that make sense *)

(* ================================================================================ *)
(** **            Q: v8 of [pred], refusing dummy implementations. *)

Locate "_ + { _ }".
Print sumor.

Locate "[ _ ]".
Print sig.
Check exist.
Notation "!!" := (inright _).
Notation "[|| x ||]" := (inleft [x]).

Definition pred_v8_raw : forall n : nat, {m : nat | S m = n} + {n = 0}.
  refine( fun n =>
    match n with
    | O => inright (eq_refl 0)
    | S n' => inleft (exist _ n' (eq_refl _ ))
    end
  ).
Defined.

Definition pred_v8 : forall n : nat, {m : nat | S m = n} + {n = 0}.
  refine( fun n =>
    match n with
    | O => !!
    | S n' => [|| n' ||]
    end
  ); trivial.
Defined.

Definition pred_dummy8 : forall n : nat, {m : nat | S m = n} + {n = 0}.
  Fail refine( fun n => ?? ).
Abort.

Eval compute in (pred_v8 4).
Eval compute in (pred_v8 1).
Eval compute in (pred_v8 0).

(* ================================================================================ *)
(** * 6.4 - Monadic Notations *)

(* ================================================================================ *)
(** **            Q: Write a version of [double_pred] using [maybe]. *)

Print maybe.

Notation "x <-- e1 ; e2" := (match e1 with
                           | Unknown _ => ??
                           | Found _ x H => e2
                           end)
(right associativity, at level 60).

Definition double_pred : forall n m : nat, {{ p | S (fst p) = n /\ S (snd p) = m}}.
  refine(
    fun n m =>
    n' <-- pred_v7 n;
    m' <-- pred_v7 m;
    [| (n', m') |]); crush.
Defined.


(* ================================================================================ *)
(** **            Q: Write a version of [double_pred] using [sumor]. *)

Print sumor.
Locate "!!". (* inright _ : sumor _ _ *)
Locate "[|| x ||]". (* inleft (exist _ x _) : sumor *)
Notation "x <--- e1 ; e2" :=
( match e1 with
| inright _ => !!
| inleft (exist _ x _) => e2
end)
(right associativity, at level 60).

Definition double_pred_sumor : forall n m : nat,
  {p | S (fst p) = n /\ S (snd p) = m}  +  {n = 0 \/ m = 0}.
  refine (
    fun n m =>
    n' <--- pred_v8 n;
    m' <--- pred_v8 m;
    [|| (n', m') ||]
  );
  try (unfold fst; unfold snd; split; assumption);
  try (left; assumption);
  try (right; assumption).
Defined.


(* ================================================================================ *)
(** * 6.5 - A Type-Checking Example *)

(** The idea here is to illustrate above techniques
    on a certified type-checker for a language
    with arithmetic and boolean expressions. *)

Inductive exp : Set :=
| E_Nat : nat -> exp
| E_Plus : exp -> exp -> exp
| E_Bool : bool -> exp
| E_And : exp -> exp -> exp
.

Inductive typ : Set :=
| T_Nat
| T_Bool
.

Inductive hasType : exp -> typ -> Prop :=
| HT_Nat : forall n : nat,
    hasType (E_Nat n) T_Nat
| HT_Plus : forall e1 e2 : exp,
    hasType e1 T_Nat
 -> hasType e2 T_Nat 
 -> hasType (E_Plus e1 e2) T_Nat
| HT_Bool : forall b : bool,
    hasType (E_Bool b) T_Bool
| HT_And : forall e1 e2 : exp,
    hasType e1 T_Bool
 -> hasType e2 T_Bool
 -> hasType (E_And e1 e2) T_Bool
.

Definition eq_type_dec : forall t1 t2 : typ, {t1 = t2} + {t1 <> t2}.
  decide equality.
Defined.

Notation "e1 ;; e2" := (if e1 then e2 else ??)
(right associativity, at level 60).

Locate "{{ _ | _ }}". (* maybe notation *)
Print maybe.
Locate "[| _  |]". (* maybe witness, for {{ t | P t }}, give [| t_witness |]*)
Locate "??". (* maybe's Unknown *)


Print hasType.

Definition typeCheck : forall e : exp, {{ t | hasType e t }}.
  Hint Constructors hasType.
  refine( fix F (e : exp) : {{ t | hasType e t }} :=
    match e return {{t | hasType e t}} with
    | E_Nat _ => [| T_Nat |]
    | E_Plus e1 e2 =>
      t1 <-- F e1; (* returns ?? if e1 can't be typed *)
      t2 <-- F e2; (* returns ?? if e1 can't be typed *) 
      eq_type_dec t1 T_Nat;;
      eq_type_dec t2 T_Nat;;

      (*
      H0 <-- eq_type_dec t1 T_Nat; (* returns ?? if it's the second ctor, i.e. [<>] *)
      H2 <-- eq_type_dec t2 T_Nat; (* returns ?? if it's the second ctor, i.e. [<>] *)
      *)
      [| T_Nat |]
    | E_Bool _ => [| T_Bool |]
    | E_And e1 e2 =>
      t1 <-- F e1;
      t2 <-- F e2;
      eq_type_dec t1 T_Bool;;
      eq_type_dec t2 T_Bool;;
      [| _ |]
    end
  );
  try subst;
  try constructor;
  try assumption.
Defined.

Eval compute in typeCheck (E_Nat 0).
Eval compute in typeCheck (E_Plus (E_Nat 0) (E_Nat 1)).
Eval compute in typeCheck (E_Plus (E_Nat 0) (E_Bool false)).
Eval compute in typeCheck (E_And (E_Bool true) (E_Bool false)).
Eval compute in typeCheck (E_And (E_Bool true) (E_Nat 42)).


Print maybe.
Locate "??".
Locate "[| _ |]".
Locate "{{ _ | _ }}".

Print sumor.
Locate "!!".
Locate "[|| _ ||]".
Locate "_ + { _ }".

Notation "e1 ;;; e2" := (if e1 then e2 else !!)
(right associativity, at level 60).

Lemma hasType_det : forall e t1, hasType e t1 ->
  forall t2, hasType e t2 -> t1 = t2.
Proof.
    induction 1; inversion 1; reflexivity.
Qed.

Definition typeCheck' : forall e : exp, {t | hasType e t} + {forall t, ~ hasType e t}.
  Hint Constructors hasType.
  Hint Resolve hasType_det.
  refine(
    fix F (e : exp) :=
      match e return {t | hasType e t} + {forall t, ~ hasType e t} with
      | E_Nat _ => [|| T_Nat ||]
      | E_Plus e1 e2 =>
        t1 <--- F e1;
        t2 <--- F e2;
        eq_type_dec t1 T_Nat;;;
        eq_type_dec t2 T_Nat;;;
        [|| T_Nat ||]
      | E_Bool _ => [|| T_Bool ||]
      | E_And e1 e2 =>
        t1 <--- F e1;
        t2 <--- F e2;
        eq_type_dec t1 T_Bool;;;
        eq_type_dec t2 T_Bool;;;
        [|| T_Bool ||]
      end
  )
  ; clear F; crush' tt hasType; eauto.
Defined.

Eval compute in typeCheck' (E_Nat 0).
Eval compute in typeCheck' (E_Plus (E_Nat 1) (E_Nat 2)).
Eval compute in typeCheck' (E_Plus (E_Nat 1) (E_Bool true)).

Eval compute in typeCheck' (E_Bool true).
Eval compute in typeCheck' (E_And (E_Bool false) (E_Bool true)).
Eval compute in typeCheck' (E_And (E_Nat 1) (E_Bool true)).
