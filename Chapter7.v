
Require Import Mycrush.
Require Import Bool Arith List.
Require Import Eqdep List Lia.
Set Implicit Arguments.

(* ================================================================================ *)
(** * 7 - General Recursion *)

(* ================================================================================ *)
(** * 7.1 - Well-Founded Recursion *)

(** Let's see how merge sort first attempt is blocked by Coq termination rules. *)

(* ================================================================================ *)
(** **            Q: Define mergeSort naively, see Coq reject it. *)

Section mergeSort_naive.
    Variable A : Set.
    Variable le : A -> A -> bool.

    (** Insert an element into a sorted list,
    preserving the sortedness *)
    Fixpoint insert' (x : A) (l : list A) : list A :=
      match l with
      | nil => x :: nil
      | h :: t =>
        if le x h
        then x :: l
        else h :: (insert' x t)
      end.

    (** Naive function to merge two sorted list *)
    Fixpoint merge' (l1 l2 : list A) : list A :=
      match l1 with
      | nil => l2
      | h :: t => merge' t (insert' h l2)
      end.
    
    (** Split a list into two of approx equal length *)
    Fixpoint split' (l : list A) : list A * list A :=
      match l with
      | nil => (nil, nil)
      | h :: nil => ((h :: nil), nil)
      | h1 :: h2 :: l' => (
        let (l1, l2) := split' l' in
        (h1 :: l1, h2 :: l2)
      )
      end.
    
    Fail Fixpoint mergeSort_naive (ls : list A) : list A :=
      let lss := split ls in
      merge' (mergeSort_naive (fst lss)) (mergeSort_naive (snd lss)).
End mergeSort_naive.

(* ================================================================================ *)
(** **            Q: Define [Acc] and [infiniteDecreasingChain] *)

(**
[Acc R x] basically says, all chains preceding x are finite.
<<
  base  --R->  a  --R->  b --R-> ... --R-> x' --R-> x
>>

since [x] is accessible, so must be [x'], [b], [a]... until some [base]
which is trivially accessible because it has no predecessor.
*)

Section Stream.
  Variable A : Type.

  CoInductive stream : Type :=
  | Cons : A -> stream -> stream
  .
End Stream.


CoInductive infiniteDecreasingChain (A : Set) (R : A -> A -> Prop) : stream A -> Prop :=
| ChainCons : forall h x s,
  (**  H1: [-2; -inf] is aninfiniteDecreasingChain *)  
  infiniteDecreasingChain R (Cons x s) ->
  (**  H2: -2 < -1    i.e. R -2 -1 *)
  R x h ->
  (**  Conclusion : [-1 ; -2 ; s]   infiniteDecreasingChain *)
  infiniteDecreasingChain R (Cons h (Cons x s))
.

(* ================================================================================ *)
(** **            Q: Prove all accessible ([Acc]) elements can't be part of an infinite decreasing chain *)

Print Acc.

Lemma noBadChain : forall (A : Set) (x : A) R, Acc R x -> 
~(exists s, infiniteDecreasingChain R (Cons x s)).
Proof.
  intros.
  unfold not.
  induction H as [x Hacc IH].
  intro Hcontra.
  inversion Hcontra.
  match goal with
  | [H : infiniteDecreasingChain _ _ |- _ ] => inversion H
  end.
  eapply IH; eauto.
Qed.

  (**
  Acc R x
  means x is linked base to some 'base' by a finite chain of R :
  base --R--> a --R--> b --R--> .... --R--> x' --R--> x

  no no it's stronger than that, 
  it doesn't just say there exists 1 chain,
  it says ALL chains preceding x are FINITE.



  By induction on the [Acc x] property.

            [?n] is accessible
  IH      --------------------------------
            (H?n: exists inf-decr-chain to ?n) -> False

            [-1] is accessible
  Goal    -------------------------------
            (H1: exists inf-decr-chain to -1) -> False


  In other words :
  Acc ?n
  IH: inf-decr-chain-to  ?n  -> False
  Acc -1
  H1 : inf-decr-chain-to  -1
  ------------------------
  False

  Apply IH, and to prove there's an inf-decr-chain-to ?n,
  you have to destruct the inf-decr-chain to -1.
  It will hive you inf-decr-chain --R--> -2 --R--> -1
  Then you exhibit -2 as the ?n and you're done.



  *)

(** A [well_founded] relation is a relation [R]
    where every element is accessible

    In other words, there is no element that's inaccessible.
    i.e. no element is part of a infinite decreasing chain.
*)

(* ================================================================================ *)
(** **            Q: Now prove that a well-founded relation can't have any inf decr chain *)

Theorem noBadChains : forall (A : Set) (R : A -> A -> Prop),
  well_founded R -> ~(exists s, infiniteDecreasingChain R s).
Proof.
  intros.
  intro Hcontra.
  inversion Hcontra.
  match goal with
  | [H : infiniteDecreasingChain _ _ |- _] => inversion H
  end.
  eapply noBadChain; eauto.
Qed.


(* ================================================================================ *)
(** **            Q: Build a well-founded relation that [mergeSort] will respect through its recursive calls *)

Section mergeSort.
  Variable A : Type.

  Variable le : A -> A -> bool.

    (** Insert an element into a sorted list,
    preserving the sortedness *)
    Fixpoint insert (x : A) (l : list A) : list A :=
      match l with
      | nil => x :: nil
      | h :: t =>
        if le x h
        then x :: l
        else h :: (insert x t)
      end.

    (** Naive function to merge two sorted list *)
    Fixpoint merge (l1 l2 : list A) : list A :=
      match l1 with
      | nil => l2
      | h :: t => merge t (insert h l2)
      end.
    
    (** Split a list into two of approx equal length *)
    Fixpoint split (l : list A) : list A * list A :=
      match l with
      | nil => (nil, nil)
      | h :: nil => ((h :: nil), nil)
      | h1 :: h2 :: l' => (
        let (l1, l2) := split l' in
        (h1 :: l1, h2 :: l2)
      )
      end.
 


  Definition lengthOrder (s1 s2 : list A) := length s1 < length s2.  

  Hint Constructors Acc.


  Require Import Lia.

  Lemma lengthOrder_wf' :
    forall len (ls : list A),
      length ls <= len ->
      Acc lengthOrder ls.
  Proof.
    unfold lengthOrder.
    induction len as [|len IH]; intros ls Hlen.
    - (* len = 0 *)
      constructor; intros ls' Hlt.
      (* impossible: length ls' < length ls <= 0 *)
      exfalso; abstract lia.
    - (* len = S len *)
      constructor; intros ls' Hlt.
      apply IH.
      (* from Hlt and Hlen, get length ls' <= len *)
      abstract lia.
  Defined.

   
  Theorem lengthOrder_wf : well_founded lengthOrder.
Proof. red; intro; eapply lengthOrder_wf'; eauto. Defined.

  Lemma split_wf : forall len ls, 2 <= length ls <= len ->
    let (ls1, ls2) := split ls in lengthOrder ls1 ls /\ lengthOrder ls2 ls.

    unfold lengthOrder; induction len; crush; do 2 (destruct ls; crush);
    destruct (le_lt_dec 2 (length ls));
    repeat (match goal with
    | [ _ : length ?E < 2 |- _ ] => destruct E
    | [ _ : S (length ?E) < 2 |- _ ] => destruct E
    | [ IH : _ |- context[split ?L] ] =>
    specialize (IH L); destruct (split L); destruct IH
    end; crush).

  Defined.


  Ltac split_wf := intros ls ?; intros; generalize (@split_wf (length ls) ls);
  destruct (split ls); destruct 1; crush.

  Lemma split_wf1 : forall ls, 2 <= length ls
  -> lengthOrder (fst (split ls)) ls.
  split_wf.
Defined.

  Lemma split_wf2 : forall ls, 2 <= length ls
  -> lengthOrder (snd (split ls)) ls.
  split_wf.
  Defined.

  Hint Resolve split_wf1 split_wf2.


  Definition mergeSort : list A -> list A.
    refine (
    Fix 
      (* (A : Type) *)
      (* list A  (implicit) *)

      (* (R : A -> A -> Prop) *)
      (* lengthOrder   (implicit)*)

      (* well_founded R -> *)
      lengthOrder_wf   

      (* forall P : A -> Type *)
      (fun (_ : list A) => list A)

      (* (forall
            x : A,
            (forall y : A, R y x -> P y)
          -> P x) 
      *)
      (fun
        (* x : A *)
        (ls : list A ) 
        (* forall y : A, R y x -> P y *)
        (self : forall ls' : list A, lengthOrder ls' ls -> list A) =>

          if le_lt_dec 2 (length ls)
          then let lss := split ls in
          merge (self (fst lss) _) (self (snd lss) _)
          else ls
      )
    )
    
    (* This is the very spot where you link you custom function
    to the general well-foundedness property guaranteeing termination.
    By proving here that all your recursive calls are "R-bound".
    *)
    ; subst lss; eauto.
  Defined.

End mergeSort.


Check Fix.
Print Fix.


(*
Theorem mergeSort_eq : forall A (le : A -> A -> bool) ls,
  mergeSort le ls = if le_lt_dec 1 (length ls)
then let lss := split ls in
merge le (mergeSort le (fst lss)) (mergeSort le (snd lss))
else ls.
intros; apply (Fix_eq (@lengthOrder_wf A le) (fun _ => list A)); intros.

match goal with
| [ |- context[match ?E with left _ => _ | right _ => _ end] ] => destruct E
end; simpl; f_equal; eauto.
Check Fix.
Defined.
*)
Print Acc.

Eval compute in (mergeSort leb (1 :: 2 :: 36 :: 8 :: 19 :: nil)).

Print Fix.
(*
Fix = fun
  (A : Type) 
  (R : A -> A -> Prop) 
  (Rwf : well_founded R) 
  (P : A -> Type)
  (F : forall x : A, (forall y : A, R y x -> P y) -> P x)
  (x : A)
  
  => Fix_F P F (Rwf x)

  : forall [A : Type]
           [R : A -> A -> Prop],
           well_founded R ->
           forall P : A -> Type,
           (forall x : A, (forall y : A, R y x -> P y) -> P x)
           -> forall x : A,
           
           P x
*)

Print Fix_F.

(* ================================================================================ *)
(** * 7.2 - Non-termination monad *)

(* ================================================================================ *)
(** **            Q:  *)

Section computation.

  Variable A : Type.

  Definition computation :=
    {f : nat -> option A | 
    forall (n : nat) (v : A), f n = Some v ->
      forall n', n' >= n -> f n' = Some v
    }.

    (** If [n] is not high enough, [f n] can return [None].
       All [n'] above a certain threshold [n] will return [Some v].
       NOTE : For all the high enough [n]'s, it's always the same [v].
    *)

  Definition runTo (m : computation) (n : nat) (v : A) :=
    (proj1_sig m) n = Some v.

  Definition run (m : computation) (v : A) :=
    exists n, runTo m n v.
  
End computation.

Section Bottom.
  Variable A : Type.

  Definition Bottom : computation A.
    refine (
      exist _ (fun _ : nat => @None A) _
    ).
    intros. discriminate.
  Defined.

  Theorem run_Bottom : forall v, ~ (run Bottom v).
    intros x H.
    unfold run in H.
    destruct H as [n Hn].
    unfold runTo in Hn.
    unfold proj1_sig in Hn.
    unfold Bottom in Hn.
    discriminate.
  Qed.
End Bottom.

Section Return.
  Variable A : Type.
  Variable v : A.

  Definition Return : computation A.
    refine (
      exist _ (fun _ => Some v) _
    ).
    intros. assumption.
  Defined.

  Theorem run_Return : run Return v.
    unfold run.
    exists 0.
    unfold runTo.
    reflexivity.
  Qed.
End Return.

Section Bind.
  Variables A B : Type.
  Variable m1 : computation A.
  Variable m2 : A -> computation B.

  (* If [m1] returns [None], the whole thing returns [None]
     Else [m1] returns [Some vb], we feed [vb] to [m2].*)
  Definition Bind : computation B.
    refine (
      exist _ (fun (n : nat) =>
        let (f1, _) := m1 in
        match f1 n with
        | None => None
        | Some v => (
          let (f2, _) := m2 v in
          f2 n
        )
        end) _
    ).
    destruct m1 as [f1 H1].
    intros n vb H n' Hge.

    destruct (f1 n) as [va |] eqn:Hf1n.
    - (* Case 1 : Some a *)
      assert (Hf1some : f1 n' = Some va). {
        eapply H1. eauto. assumption.
      }
      rewrite Hf1some.
      destruct (m2 va) as [f2 H2].
      eapply H2; crush.
    -  (* Case 2 : None *)
      discriminate.
  Defined.
End Bind.

Check Bind.

Notation "x <- m1 ; m2" :=
  (Bind m1 (fun x => m2)) (right associativity, at level 70).

Definition meq (A : Type) (m1 m2 : computation A) :=
  forall n : nat, proj1_sig m1 n = proj1_sig m2 n.

