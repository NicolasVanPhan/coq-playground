
(** printing token %...LATEX...% #...HTML...# *)

Require Import Mycrush.

(* begin hide *)

Require Import Eqdep List Lia.

Set Implicit Arguments.

(** A version of [injection] that does some standard simplifications afterward: clear the hypothesis in question, bring the new facts above the double line, and attempt substitution for known variables. *)
Ltac inject H := injection H; clear H; intros; try subst.

(** Try calling tactic function [f] on all hypotheses, keeping the first application that doesn't fail. *)
Ltac appHyps f :=
  match goal with
    | [ H : _ |- _ ] => f H
  end.

(** Succeed iff [x] is in the list [ls], represented with left-associated nested tuples. *)
Ltac inList x ls :=
  match ls with
    | x => idtac
    | (_, x) => idtac
    | (?LS, _) => inList x LS
  end.

(** Try calling tactic function [f] on every element of tupled list [ls], keeping the first call not to fail. *)
Ltac app f ls :=
  match ls with
    | (?LS, ?X) => f X || app f LS || fail 1
    | _ => f ls
  end.

(** Run [f] on every element of [ls], not just the first that doesn't fail. *)
Ltac all f ls :=
  match ls with
    | (?LS, ?X) => f X; all f LS
    | (_, _) => fail 1
    | _ => f ls
  end.

(** Workhorse tactic to simplify hypotheses for a variety of proofs.
   * Argument [invOne] is a tuple-list of predicates for which we always do inversion automatically. *)
Ltac simplHyp invOne :=
  (** Helper function to do inversion on certain hypotheses, where [H] is the hypothesis and [F] its head symbol *)
  let invert H F :=
    (** We only proceed for those predicates in [invOne]. *)
    inList F invOne;
    (** This case covers an inversion that succeeds immediately, meaning no constructors of [F] applied. *)
      (inversion H; fail)
    (** Otherwise, we only proceed if inversion eliminates all but one constructor case. *)
      || (inversion H; [idtac]; clear H; try subst) in

  match goal with
    (** Eliminate all existential hypotheses. *)
    | [ H : ex _ |- _ ] => destruct H

    (** Find opportunities to take advantage of injectivity of data constructors, for several different arities. *)
    | [ H : ?F ?X = ?F ?Y |- ?G ] =>
      (** This first branch of the [||] fails the whole attempt iff the arguments of the constructor applications are already easy to prove equal. *)
      (assert (X = Y); [ assumption | fail 1 ])
      (** If we pass that filter, then we use injection on [H] and do some simplification as in [inject].
         * The odd-looking check of the goal form is to avoid cases where [injection] gives a more complex result because of dependent typing, which we aren't equipped to handle here. *)
      || (injection H;
        match goal with
          | [ |- X = Y -> G ] =>
            try clear H; intros; try subst
        end)
    | [ H : ?F ?X ?U = ?F ?Y ?V |- ?G ] =>
      (assert (X = Y); [ assumption
        | assert (U = V); [ assumption | fail 1 ] ])
      || (injection H;
        match goal with
          | [ |- U = V -> X = Y -> G ] =>
            try clear H; intros; try subst
        end)

    (** Consider some different arities of a predicate [F] in a hypothesis that we might want to invert. *)
    | [ H : ?F _ |- _ ] => invert H F
    | [ H : ?F _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ |- _ ] => invert H F
    | [ H : ?F _ _ _ _ _ |- _ ] => invert H F

    (** Use an (axiom-dependent!) inversion principle for dependent pairs, from the standard library. *)
    | [ H : existT _ ?T _ = existT _ ?T _ |- _ ] => generalize (inj_pair2 _ _ _ _ _ H); clear H

    (** If we're not ready to use that principle yet, try the standard inversion, which often enables the previous rule. *)
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] => inversion H; clear H

    (** Similar logic to the cases for constructor injectivity above, but specialized to [Some], since the above cases won't deal with polymorphic constructors. *)
    | [ H : Some _ = Some _ |- _ ] => injection H; clear H
  end.

(** Find some hypothesis to rewrite with, ensuring that [auto] proves all of the extra subgoals added by [rewrite]. *)
Ltac rewriteHyp :=
  match goal with
    | [ H : _ |- _ ] => rewrite H by solve [ auto ]
  end.

(** Combine [autorewrite] with automatic hypothesis rewrites. *)
Ltac rewriterP := repeat (rewriteHyp; autorewrite with core in *).
Ltac rewriter := autorewrite with core in *; rewriterP.

(** This one is just so darned useful, let's add it as a hint here. *)
Hint Rewrite app_ass.

(** Devious marker predicate to use for encoding state within proof goals *)
Definition done (T : Type) (x : T) := True.

(** Try a new instantiation of a universally quantified fact, proved by [e].
   * [trace] is an accumulator recording which instantiations we choose. *)
Ltac inster e trace :=
  (** Does [e] have any quantifiers left? *)
  match type of e with
    | forall x : _, _ =>
      (** Yes, so let's pick the first context variable of the right type. *)
      match goal with
        | [ H : _ |- _ ] =>
          inster (e H) (trace, H)
        | _ => fail 2
      end
    | _ =>
      (** No more quantifiers, so now we check if the trace we computed was already used. *)
      match trace with
        | (_, _) =>
          (** We only reach this case if the trace is nonempty, ensuring that [inster] fails if no progress can be made. *)
          match goal with
            | [ H : done (trace, _) |- _ ] =>
              (** Uh oh, found a record of this trace in the context!  Abort to backtrack to try another trace. *)
              fail 1
            | _ =>
              (** What is the type of the proof [e] now? *)
              let T := type of e in
                match type of T with
                  | Prop =>
                    (** [e] should be thought of as a proof, so let's add it to the context, and also add a new marker hypothesis recording our choice of trace. *)
                    generalize e; intro;
                      assert (done (trace, tt)) by constructor
                  | _ =>
                    (** [e] is something beside a proof.  Better make sure no element of our current trace was generated by a previous call to [inster], or we might get stuck in an infinite loop!  (We store previous [inster] terms in second positions of tuples used as arguments to [done] in hypotheses.  Proofs instantiated by [inster] merely use [tt] in such positions.) *)
                    all ltac:(fun X =>
                      match goal with
                        | [ H : done (_, X) |- _ ] => fail 1
                        | _ => idtac
                      end) trace;
                    (** Pick a new name for our new instantiation. *)
                    let i := fresh "i" in (pose (i := e);
                      assert (done (trace, i)) by constructor)
                end
          end
      end
  end.

(** After a round of application with the above, we will have a lot of junk [done] markers to clean up; hence this tactic. *)
Ltac un_done :=
  repeat match goal with
           | [ H : done _ |- _ ] => clear H
         end.

Require Import JMeq.

(** A more parameterized version of the famous [crush].  Extra arguments are:
   * - A tuple-list of lemmas we try [inster]-ing 
   * - A tuple-list of predicates we try inversion for *)
Ltac crush' lemmas invOne :=
  (** A useful combination of standard automation *)
  let sintuition := simpl in *; intuition; try subst;
    repeat (simplHyp invOne; intuition; try subst); try congruence in

  (** A fancier version of [rewriter] from above, which uses [crush'] to discharge side conditions *)
  let rewriter := autorewrite with core in *;
    repeat (match goal with
              | [ H : ?P |- _ ] =>
                match P with
                  | context[JMeq] => fail 1 (** JMeq is too fancy to deal with here. *)
                  | _ => rewrite H by crush' lemmas invOne
                end
            end; autorewrite with core in *) in

  (** Now the main sequence of heuristics: *)
    (sintuition; rewriter;
      match lemmas with
        | false => idtac (** No lemmas?  Nothing to do here *)
        | _ =>
          (** Try a loop of instantiating lemmas... *)
          repeat ((app ltac:(fun L => inster L L) lemmas
          (** ...or instantiating hypotheses... *)
            || appHyps ltac:(fun L => inster L L));
          (** ...and then simplifying hypotheses. *)
          repeat (simplHyp invOne; intuition)); un_done
      end;
      sintuition; rewriter; sintuition;
      (** End with a last attempt to prove an arithmetic fact with [lia], or prove any sort of fact in a context that is contradictory by reasoning that [lia] can do. *)
      try lia; try (exfalso; lia)).

(** [crush] instantiates [crush'] with the simplest possible parameters. *)
Ltac crush := crush' false fail.

(** * Wrap Program's [dependent destruction] in a slightly more pleasant form *)

Require Import Program.Equality.

(** Run [dependent destruction] on [E] and look for opportunities to simplify the result.
   The weird introduction of [x] helps get around limitations of [dependent destruction], in terms of which sorts of arguments it will accept (e.g., variables bound to hypotheses within Ltac [match]es). *)
Ltac dep_destruct E :=
  let x := fresh "x" in
    remember E as x; simpl in x; dependent destruction x;
      try match goal with
            | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
          end.

(** Nuke all hypotheses that we can get away with, without invalidating the goal statement. *)
Ltac clear_all :=
  repeat match goal with
           | [ H : _ |- _ ] => clear H
         end.

(** Instantiate a quantifier in a hypothesis [H] with value [v], or, if [v] doesn't have the right type, with a new unification variable.
   * Also prove the lefthand sides of any implications that this exposes, simplifying [H] to leave out those implications. *)
Ltac guess v H :=
  repeat match type of H with
           | forall x : ?T, _ =>
             match type of T with
               | Prop =>
                 (let H' := fresh "H'" in
                   assert (H' : T); [
                     solve [ eauto 6 ]
                     | specialize (H H'); clear H' ])
                 || fail 1
               | _ =>
                 specialize (H v)
                 || let x := fresh "x" in
                   evar (x : T);
                   let x' := eval unfold x in x in
                     clear x; specialize (H x')
             end
         end.

(** Version of [guess] that leaves the original [H] intact *)
Ltac guessKeep v H :=
  let H' := fresh "H'" in
    generalize H; intro H'; guess v H'.

(* end hide *)

(* begin hide *)


Require Import Bool Arith List.
Set Implicit Arguments.
Set Asymmetric Patterns.

Theorem t : forall P : Prop, P -> P.
Proof.
  crush.
Qed.

Check (fun x : nat => x).
Check (fun x : True => x).

Inductive unit : Set := tt : unit.

Check (unit_ind : forall P : unit -> Prop, P tt -> forall x : unit, P x).

Theorem the_sky_is_falling : forall x : Empty_set, 2 + 2 = 5.
Proof.
  destruct 1.
Qed.

Module Bool'.

Inductive bool' : Set :=
| true : bool'
| false : bool'
.

Definition negb' : bool' -> bool' :=
  fun b => match b with
    | true => false
    | false => true
  end.

Theorem negb'_involutive : forall b : bool', negb'( negb' b ) = b.
Proof.
  destruct b ; reflexivity.
Qed.

Check (bool'_ind : forall P : bool' -> Prop, P true -> P false -> forall x : bool', P x).

End Bool'.

Inductive nat' : Set :=
| O' : nat'
| S' : nat' -> nat'
.

Theorem S_inj : forall x y : nat', S' x = S' y -> x = y.
Proof.
  injection 1.
  trivial.
Qed.

(* Define the nat list type (just for nats) *)
Inductive natlist : Set :=
| NNil : natlist
| NCons : nat -> natlist -> natlist
.

Check (natlist_ind :
      forall P : natlist -> Prop,
      P NNil ->
      (forall n l, P l -> P (NCons n l)) ->
      forall l : natlist, P l).

(* The following :
     Fixpoint nlength : natlist -> nat := .. ..
   raises :
     A fixpoint needs at least one parameter. *)

Fixpoint nlength (l : natlist) : nat :=
  match l with
  | NNil => O
  | NCons _ l' => S (nlength l')
  end.

Fixpoint napp (l1 l2 : natlist) : natlist :=
  match l1 with
  | NNil => l2
  | NCons h t => NCons h (napp t l2)
  end.


Inductive nat_btree : Set :=
| NLeaf : nat_btree
| NNode : nat -> nat_btree -> nat_btree -> nat_btree
.

Check (nat_btree_ind :
  forall P : nat_btree -> Prop,
    P NLeaf ->
    (forall n t1, P t1 -> forall t2, P t2 -> P (NNode n t1 t2)) ->
    forall t : nat_btree, P t).



Inductive list' (T : Set) : Set :=
| Nil' : list' T
| Cons' : T -> list' T -> list' T
.

Fixpoint length' (T : Set) (l : list' T) : nat :=
  match l with
  | Nil' => O
  | Cons' _ l' => S ( length' l' )
  end.

Fixpoint app' (T : Set) (l1 l2 : list' T) : list' T :=
  match l1 with
  | Nil' => l2
  | Cons' h t => Cons' h (app' t l2)
  end.

(* Now using section *)

Section list3.

  Variable T : Set.

  Inductive list3 : Set :=
  | Nil3 : list3
  | Cons3 : T -> list3 -> list3
  .

  Fixpoint length3 (l : list3) : nat :=
    match l with
    | Nil3 => O
    | Cons3 _ t => S (length3 t)
    end.

  Fixpoint app3 (l1 l2 : list3) : list3 :=
    match l1 with
    | Nil3 => l2
    | Cons3 h t => Cons3 h (app3 t l2)
    end.
End list3.

Arguments Nil3 {T}.

Check (list3_ind :
        forall T : Set,
        forall P : list3 T -> Prop,
          P Nil3 ->
          (forall (x : T) (l : list3 T), P l -> P (Cons3 x l)) ->
          forall l : list3 T, P l).


(* Mutually inductive types *)

Inductive even_list : Set :=
| ENil : even_list
| ECons : nat -> odd_list -> even_list

with odd_list : Set :=
| OCons : nat -> even_list -> odd_list
.

Check (even_list_ind :
        forall P : even_list -> Prop,
        P ENil ->
        (forall n : nat, forall l : odd_list, (* No P l *) P (ECons n l)) ->
        forall l : even_list, P l
       ).

Fixpoint elength (l : even_list) : nat :=
  match l with
  | ENil => O
  | ECons _ ol => S (olength ol)
  end

with olength (l : odd_list) : nat :=
  match l with
  | OCons _ el => S (elength el)
  end.

Eval compute in (olength
                   (OCons 8
                      (ECons 5
                         (OCons 2 (ENil))))).

(* For a given list you can't call length, you have to calll
   wither elength or olength depending on the type of the list,
   that's not very convenient... *)

Fixpoint eapp (el1 el2 : even_list) : even_list :=
  match el1 with
  | ENil => el2
  | ECons n ol => ECons n (oapp ol el2)
  end

with oapp (ol : odd_list) (el : even_list) : odd_list :=
  match ol with
  | OCons n el' => OCons n (eapp el' el)
  end.

(* The length of the sum is the sum of the lengths *)
Theorem e_app_len : forall l1 l2 : even_list, elength (eapp l1 l2) = (elength l1) + (elength l2).
Proof.
  intros.
  induction l1; crush.
(*   ============================ *)
(*   S (olength (oapp o l2)) = S (olength o + elength l2) *)
  induction o; crush.
(*   ============================ *)
(*   S (S (elength (eapp e l2))) = S (S (elength e + elength l2)) *)
(* ... *)
(* We're missing a mutually inductive principle here. *)
Abort.

Scheme even_list_mut := Induction for even_list Sort Prop
with   odd_list_mut  := Induction for odd_list Sort Prop.



Check (even_list_mut :
  forall Pe : even_list -> Prop,
  forall Po : odd_list  -> Prop,
  Pe ENil ->
  (forall n : nat, forall ol : odd_list,  Po ol -> Pe (ECons n ol)) ->
  (forall n : nat, forall el : even_list, Pe el -> Po (OCons n el)) ->
  forall l : even_list, Pe l
).

Theorem e_app_len' : forall l1 l2 : even_list, elength (eapp l1 l2) = (elength l1) + (elength l2).
Proof.
  intros.
  apply (even_list_mut
           (fun l1 : even_list => forall l2 : even_list, elength (eapp l1 l2) = (elength l1) + (elength l2))
           (fun l1 : odd_list => forall l2 : even_list, olength (oapp l1 l2) = (olength l1) + (elength l2))
  ); crush.
Qed.

Inductive pf : Set :=
| Truth  : pf
| Falsehood  : pf
| Conjunction : pf -> pf -> pf
.

Fixpoint pfDenote (e : pf) : Prop :=
  match e with
  | Truth => True
  | Falsehood => False
  | Conjunction e1 e2 => (pfDenote e1) /\ (pfDenote e2)
  end.

Inductive formula : Set :=
| Eq : nat -> nat -> formula
| And : formula -> formula -> formula
| Forall : (nat -> formula) -> formula  (* Delegating management of variables to Coq  c/f. PHOAS *)
.

Fixpoint fDenote (f : formula) : Prop :=
  match f with
  | Eq n1 n2 => n1 = n2
  | And f1 f2 => (fDenote f1) /\ (fDenote f2)
  | Forall ntof => forall n : nat, fDenote (ntof n)  (* HOAS : Variables are represented with *)
  end.

(* Object language                            :    Forall (fun x => FORMULA_AST x) *)
(* Denotation (i.e. semantics in Coq's logic  : {{ Forall (fun  x => FORMULA_AST x) }} *)
(*                                                 forall x, {{ FORMULA_AST x       }} *)

Fixpoint swapper (f : formula) : formula :=
  match f with
  | Eq n1 n2 => Eq n2 n1
  | And f1 f2 => And (swapper f1) (swapper f2)
  | Forall ntof => Forall (fun n => swapper (ntof n))
  end.

Theorem swapper_preserved_truth : forall f : formula, fDenote f -> fDenote (swapper f).
Proof.
  induction f; crush.
Qed.

Check formula_ind.

(* Inductive term : Set := *)
(* | LApp : term -> term -> term   (* f x             <---> LApp f x     *) *)
(* | LAbs : (term -> term) -> term (* lambda x . x^2  <---> fun x -> x^2 *) *)
(* . *)

(* (* This would run forever, which would break the Coq logic *) *)
(* Definition uhoh (t : term) : term := *)
(*   match t with *)
(*   | LAbs f -> f t *)
(*   | _ => t *)
(* end. *)

Definition nat_rec_type :=
        forall P : nat -> Prop,
          P O ->
          (forall n : nat, P n -> P (S n)) ->
          (forall n : nat, P n).

Check (nat_rec : nat_rec_type).

Fixpoint my_nat_rec
  (P : nat -> Prop)
  (HPO : P O)
  (HPS : forall n : nat, P n -> P (S n))
  (n : nat)
  : P n :=
      match n as n0 return P n0 with
        | O => HPO                   (* : P O *)
        | S n' => HPS n' (my_nat_rec P HPO HPS n')    (* : P (S n') *)
      end
    .

Check (my_nat_rec : nat_rec_type).

Definition my_nat_rec' : nat_rec_type :=
  fun (P : nat -> Prop)
    (HPO : P O)
    (HPS : forall n : nat, P n -> P (S n)) =>
    (fix aux (n : nat) : P n :=
       match n with
         | O => HPO                   (* : P O *)
         | S n' => HPS n' (aux n')    (* : P (S n') *)
       end
    ).

Section nat_ind'.

Variable P : nat -> Prop.
Hypothesis HPO : P O.
Hypothesis HPS : (forall n : nat, P n -> P (S n)).


Fixpoint nat_ind' (n : nat) : P n :=
  match n as m return P m with
  | O => (HPO : P O)
  | S n' => (HPS (nat_ind' n') : P (S n'))
  end.

End nat_ind'.

Section even_list_mut'.

  Hypothesis Peven : even_list -> Prop.
  Hypothesis Podd : odd_list -> Prop.

  Hypothesis HENil : Peven ENil.
  Hypothesis HECons : forall n : nat, forall l : odd_list, Podd l -> Peven (ECons n l).
  Hypothesis HOCons : forall n : nat, forall l : even_list, Peven l -> Podd (OCons n l).

  Fixpoint even_list_mut' (l : even_list) : Peven l :=
    match l with
    | ENil => HENil
    | ECons n ol => HECons n (odd_list_mut' ol)
    end
  with odd_list_mut' (l : odd_list) : Podd l :=
    match l with
    | OCons n el => HOCons n (even_list_mut' el)
    end.

End even_list_mut'.

Check even_list_mut'.

Inductive binary_tree : Set :=
| BNode : bool -> list binary_tree -> binary_tree
.

Check binary_tree_ind.

Inductive nat_tree : Set :=
| NNode' : nat -> list nat_tree -> nat_tree
.

Check nat_tree_ind.

(* Predicate taking :
 - a prop P
 - a list l = e1 ; e2; e3 ... ; en ; Nil
returning :
   P e1 /\ P e2 /\ P e3 /\ ... /\ P en /\ True
*)

Section All.
  Variable T : Set. (* list element : nat, bool, whatever *)
  Hypothesis P : T -> Prop.

  Print list.

  Fixpoint All (l : list T) : Prop :=
    match l with
    | nil => True
    | cons h t => P h /\ (All t)
    end.

End All.

Check   (All (Nat.eq 42) (30 :: 42 :: 50 :: nil)).
(* All (Nat.eq 42) (30 :: 42 :: 50 :: nil) *)
(*      : Prop *)
Compute (All (Nat.eq 42) (30 :: 42 :: 50 :: nil)).
(* = 42 = 30 /\ 42 = 42 /\ 42 = 50 /\ True *)
(* : Prop *)

Print True.
Locate "/\".
Print and.


(* Now let's build that custom induction principle *)

Section nat_tree_ind'.
  
  Variable P : nat_tree -> Prop.

  Hypothesis HNNode' :
    forall n : nat,
    forall l : list nat_tree,
    (All P l) ->  (* All elements of the list satisfy P *)
    P (NNode' n l).

  (* Here's a first attempt that works, but is not very readable...
     and turns out the CPDT book doesn't offer more readable solutions :O *)
  Fixpoint nat_tree_ind' (t : nat_tree) : P t :=
    match t with
    | NNode' n l => HNNode' n l (
        list_ind
          (fun t => All P t)
          (I : All P nil)
          (fun h t IH => conj (nat_tree_ind' h) IH)
          l)
    end.

End nat_tree_ind'.


  (* Now here's a more readable attempt from the CPDT book... that doesn't work ! *)
  (* Fixpoint nat_tree_ind' (t : nat_tree) : P t :=
    match t with
    | NNode' n l => HNNode' n l (list_nat_tree_ind' l)
    end
  
  with list_nat_tree_ind' (l : list nat_tree) : All P l :=
    match l with
    | nil => I
    | cons h t => conj (nat_tree_ind' h) (list_nat_tree_ind' t)
    end.   *)
  
(*  ERROR message :
Recursive call to nat_tree_ind' has principal argument equal to 
"h" instead of "t".

What CPDT says about it :

There is no deep theoretical reason why this program should be rejected; Coq applies
incomplete termination-checking heuristics, and it is necessary to learn a few of the most
62
important rules. The term “nested inductive type” hints at the solution to this particular
problem. Just as mutually inductive types require mutually recursive induction principles,
nested types require nested recursion.
*)

Section nat_tree_ind''.

    Variable P : nat_tree -> Prop.

  Hypothesis HNNode' :
    forall n : nat,
    forall l : list nat_tree,
    (All P l) ->  (* All elements of the list satisfy P *)
    P (NNode' n l).

  Fixpoint nat_tree_ind'' (t : nat_tree) : P t :=
    match t with
    | NNode' n l => HNNode' n l
      ((fix list_nat_tree_ind'' (l : list nat_tree) : All P l :=
         match l with
         | nil => I
         | cons h t => conj (nat_tree_ind'' h) (list_nat_tree_ind'' t)
         end
      ) l)
    end.
    
End nat_tree_ind''.

(* end hide *)




(** * 3.8 - Nested Inductive Types *)

Module Nested_inductive_types.

(** **           Q: Give an example of nested inductive type *)
(** #</div><details><summary>Answer</summary><div class="doc"># *)

Inductive nat_tree : Set :=
| NNode : nat -> list nat_tree -> nat_tree
.

(* -------------------------------------------------------------------------------- *)
(** **           Q: Why is it called "nested" ? *)
(**              #</div><details><summary>Answer</summary><div class="doc"># *)

(**
Because it uses the type we're defining (here [nat_tree])
as an argument to a parametrized type family (here [list]).
*)

(* -------------------------------------------------------------------------------- *)
(** **           Q: What's the problem with it ? *)
(**              #</div><details><summary>Answer</summary><div class="doc"># *)

(**
Not all nested inductive type definitions will be allowed.
Some will violate the positivity rule.
*)

(* -------------------------------------------------------------------------------- *)
(** **           Q: Give an example of type definition violating the positivity rule *)
(**              #</div><details><summary>Answer</summary><div class="doc"># *)

(** TODO : Answer this one *)

(** # </div> </details> <div class="doc"> # *)

(* -------------------------------------------------------------------------------- *)
(** **           Q: What is the usual problem with nested inductive types ? *)
(**              #</div><details><summary>Answer</summary><div class="doc"># *)

(**
The generated induction principle is too weak,
so we have to manually write a more powerful one.
*)

(* -------------------------------------------------------------------------------- *)
(** **           Q: Give the default generate induction principle *)
(**              #</div><details><summary>Answer</summary><div class="doc"># *)


Check (nat_tree_ind :
  forall P : nat_tree -> Prop,                              (* predicate *)
    (forall (n : nat) (l : list nat_tree), P (NNode n l))   (* NNode hypotesis *)
    -> forall t : nat_tree, P t                             (* final goal *)
).


(* -------------------------------------------------------------------------------- *)
(** **           Q: *)
(**              #</div><details><summary>Answer</summary><div class="doc"># *)



(* -------------------------------------------------------------------------------- *)
(**              # </div> </details> <div class="doc"> # *)
(**              # </div> </details> <div class="doc"> # *)
(**              # </div> </details> <div class="doc"> # *)
(**              # </div> </details> <div class="doc"> # *)
(**              # </div> </details> <div class="doc"> # *)
(**              # </div> </details> <div class="doc"> # *)

End Nested_inductive_types.



(** * 3.9 - Manual Proofs about Constructors *)

  (**
  
  What are True and False ?

  > They are logical propositions ?

  Okay, what are logicial propositions concretely ?

  > They are types (whose inhabitants are the proofs for those propositions)
  > They are values (of type Prop)

  What's so special about Prop / Set / Type ?
  Why can't we define True as before but with : Set instead of : Prop ?

  *)

Definition toProp (b : bool) := if b then True else False.


Theorem true_neq_false : True <> False.
Proof.
  red.
  intro H.
  
  (* Replace True (resp False) with "toProp true" (resp false) *)

  assert (Ht : True = toProp true). { reflexivity. }
  assert (Hf : False = toProp false). { reflexivity. }
  rewrite Ht in *.
  rewrite Hf in *.

  rewrite <- H.
  rewrite <- Ht.
  exact I.
Qed.


