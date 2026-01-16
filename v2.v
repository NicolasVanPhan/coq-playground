

Require Import Mycrush.
From Coq Require Import Bool String List Arith NArith Ascii.
From Coq Require Import Vectors.Vector.
Open Scope N_scope.

Inductive bit : Set :=
| b0 : bit
| b1 : bit.

(**

Let's think on paper before proving.
You want a function to translate between the [N] and [Vector.t bool] representation of this value.

Take 26 as an example :
16 + 8 + 2 = 26 = 0x1A = 0b11010

The [N] representation is xO xI xO xI xI (like the binary representation, but LSB first)

The reversed Vector.t representation would be [bO bI bO bI bI]

<<
(Vector.cons _ b0 _ 
(Vector.cons _ b1 _ 
(Vector.cons _ b0 _ 
(Vector.cons _ b1 _ 
(Vector.cons _ b1 _
(Vector.nil  _ )))))).
>>

how to translate :

26 = 0 + 2 + 8 + 16
   = 0 + 2^1 + 2^3 + 2^4


vec_of_N(0%N,  5) = [b0 b0 b0 b0 b0]
vec_of_N(1%N,  5) = [b1 b0 b0 b0 b0]
vec_of_N(26%N, 5) = [b0 b1 b0 b1 b1]

vec_of_N(Npos xO xI xO xI xI, 5) = [b0 b1 b0 b1 b1]

vec_of_N(Npos xO xI xO xI xI, 5) = [b0 b1 b0 b1 b1]

vec_of_pos(xH, 1) = [b1]
vec_of_pos(xH, 2) = [b1 b0]
vec_of_pos(xH, 3) = [b1 b0 b0]


vec_of_pos(xH, 1) = [b1]

vec_of_pos(xI xH, 2) = [b1 ; b1]
vec_of_pos(xI xH, 2) = b1 :: vec_of_pos (xH, 1)

vec_of_pos(xO xI xH, 3) = [b0 ; b1 ; b1]
vec_of_pos(xO xI xH, 3) = b0 :: vec_of_pos(xI xH, 2)

Look like the pattern appears :
vec_of_pos(x :: tail, w) = x_to_bit(x) :: vec_of_pos(tail, w-1)

--- But what if the target width is not 3 but bigger ?

vec_of_pos(xO xI xH, 5) = [b0 ; b1 ; b1; b0; b0]
= x2b(xO) :: vec_of_pos(xI xH, 4)
= x2b(xO) :: x2b(xI) :: vec_of_pos(xH, 3)
= x2b(xO) :: x2b(xI) :: x2b(xH) :: vec_of_pos(<what to put here>, 2)

We want to convey 'no more bit to give you',
perhaps using the option type would be nice here ?

= x2b(xO) :: x2b(xI) :: x2b(xH) :: vec_of_pos(None, 2)
= x2b(xO) :: x2b(xI) :: x2b(xH) :: b0 :: vec_of_pos(None, 1)
= x2b(xO) :: x2b(xI) :: x2b(xH) :: b0 :: b0 :: vec_of_pos(None, 0)
= x2b(xO) :: x2b(xI) :: x2b(xH) :: b0 :: b0 :: nil

We end up with this terminal case :
- If the pos is None, we return a [b0] and recursively call with [w-1]
- If the width is 0, we return [nil]

--- And what if the width is smaller than 3 ?

We want to truncate the MSBs

vec_of_pos(xO xI xH, 2) = [b0 ; b1]
= x2b(xO) :: vec_of_pos(xI xH, 1)
= x2b(xO) :: x2b(xI) :: vec_of_pos(xH, 0)
= x2b(xO) :: x2b(xI) :: nil

Actually we already have this case :
- If the width is 0, we return [nil]

--- In summary, we end up with these three clauses :

vec_of_pos( _ , O) = nil
vec_of_pos( None , S w' ) = b0 :: vec_of_pos( None, w' )
vec_of_pos( Some (x :: tail) , S w' ) = x2b(x) :: vec_of_pos( Some tail, w' )

Let's try to implement that as a fixpoint.
*)


Fixpoint vec_of_pos (w : nat) (p_opt : option positive) : Vector.t bit w :=
  match p_opt, w with
  | _           , O    => Vector.nil _
  | None        , S w' => Vector.cons _ b0 w' (vec_of_pos w' None)
  | Some (xH)   , S w' => Vector.cons _ b1 w' (vec_of_pos w' None)
  | Some (xO p'), S w' => Vector.cons _ b0 w' (vec_of_pos w' (Some p'))
  | Some (xI p'), S w' => Vector.cons _ b1 w' (vec_of_pos w' (Some p'))
  end.

Theorem vec_of_pos_sanity0 :
  forall p : positive, vec_of_pos 0 (Some p) = Vector.nil _.
Proof. intro p. simpl. destruct p; reflexivity. Qed.

(** TODO : Why must I destruct [p] here ?? Result should evaluate to [nil] without even looking at [p] *)

Theorem vec_of_pos_sanity1 :
  vec_of_pos 1 (Some xH) = cons _ b1 _ (nil _).
Proof. reflexivity. Qed.

Theorem vec_of_pos_sanity2 :
  vec_of_pos 3 (None) = cons _ b0 _ 
                       ( cons _ b0 _ 
                       ( cons _ b0 _ 
                       ( nil _ ))).
Proof. reflexivity. Qed.

Theorem vec_of_pos_sanity3 :
  vec_of_pos 3 (Some (xO (xI (xH)))) =
    ( cons _ b0 _ 
    ( cons _ b1 _ 
    ( cons _ b1 _ 
    ( nil _ )))).
Proof. reflexivity. Qed.

Theorem vec_of_pos_sanity4 :
  vec_of_pos 5 (Some (xO (xI (xH)))) =
    ( cons _ b0 _ 
    ( cons _ b1 _ 
    ( cons _ b1 _ 
    ( cons _ b0 _ 
    ( cons _ b0 _ 
    ( nil _ )))))).
Proof. reflexivity. Qed.


(** Now let's wrap it in [vec_of_N] *)

Fixpoint vec_zeroes (w : nat) : Vector.t bit w :=
  match w with
  | O => Vector.nil _
  | S w' => Vector.cons _ b0 _ (vec_zeroes w')
  end.

Theorem vec_zeroes_sanity0 : vec_zeroes 0 = Vector.nil _. reflexivity. Qed.
Theorem vec_zeroes_sanity3 :
  vec_zeroes 3 =
    ( cons _ b0 _ 
    ( cons _ b0 _ 
    ( cons _ b0 _ 
    ( nil _ )))).
Proof. reflexivity. Qed.

Definition vec_of_N (w : nat) (n : N) : Vector.t bit w :=
  match n with
  | N0 => vec_zeroes w
  | Npos p => vec_of_pos w (Some p)
  end.


Eval compute in vec_of_N 5 26.

Theorem vec_of_N_sanity_26 :
  vec_of_N 5 26 = 
  ( cons _ b0 _ 
  ( cons _ b1 _ 
  ( cons _ b0 _ 
  ( cons _ b1 _ 
  ( cons _ b1 _ 
  ( nil _)))))).
Proof. reflexivity. Qed.

Theorem vec_of_N_sanity_26_ext :
  vec_of_N 7 26 = 
  ( cons _ b0 _ 
  ( cons _ b1 _ 
  ( cons _ b0 _ 
  ( cons _ b1 _ 
  ( cons _ b1 _ 
  ( cons _ b0 _ 
  ( cons _ b0 _ 
  ( nil _)))))))).
Proof. reflexivity. Qed.

Theorem vec_of_N_sanity_26_trunc :
  vec_of_N 3 26 = 
  ( cons _ b0 _ 
  ( cons _ b1 _ 
  ( cons _ b0 _ 
  ( nil _ )))).
Proof. reflexivity. Qed.
 

(** Alright, seems good so far ! Let's write the reverse now.

How would it work ?
Let's write the spec in terms of clauses f(x) = y as above.

f = N_of_vec

f(b0, 1) = 0 = N0
f(b0 b1 b0 b1 b1, 5) = 26 = Npos (xO xI xO xI xH)

Let's try to make a recursive pattern appear :
<<
f(   b1 b0 b1 b1, 4) = 13 = 26 / 2 
f(      b0 b1 b1, 3) = 6  = 13 / 2
f(         b1 b1, 2) = 3  = 6  / 2
f(            b1, 1) = 1  = 3  / 2
>>

So :
<<
f(b0 b1 b0 b1 b1, 5) = 26 
  = 2 * 13
  = 2 * f(b1 b0 b1 b1, 4)
  = 2 * (1 + 2 * 6)
  = 2 * (1 + 2 * f(b0 b1 b1, 3))
  = 0 + 2 * (1 + 2 * f(b0 b1 b1, 3))
  = 0 + 2 * (1 + 2 * (0 + 2 * f(b1 b1, 2)))
  = 0 + 2 * (1 + 2 * (0 + 2 * (1 + 2 * f(b1, 1)))))
  = 0 + 2 * (1 + 2 * (0 + 2 * (1 + 2 * (1 + 2 * f(nil, 0)))))
  = 0 + 2 * (1 + 2 * (0 + 2 * (1 + 2 * (1 + 2 * 0)))))
  = 0 + 2 * (1 + 2 * (0 + 2 * (1 + 2 * 1)))))
  = 0 + 2 * (1 + 2 * (0 + 2 * (1 + 2)))))
  = 0 + 2 * (1 + 2 * (0 + 2 * 3))
  = 0 + 2 * (1 + 2 * 6)
  = 0 + 2 * (1 + 12)
  = 0 + 2 * 13
  = 26
>>

And we can see the recursive pattern emerge :
<<
A: f(b :: bs, S w) = b + 2 * f(bs, w)
>>

with the base case :
<<
B: f(b, 0) = 0
>>

Note : To terminate recursion 1 step earlier, we can also state :
<<
B': f(b, 1) = b
>>
But it's not necessary here

-- What happens on vectors with leading zeroes ?

<<
f(b0 b1 b0 b1 b1 b0 b0, 7) = 26
 = 0 + 2 * f(b1 b0 b1 b1 b0 b0, 6)
 = ...
 = 0 + 2 * (1 + 2 * (0 + 2 * (1 + 2 * f(b1 b0 b0, 3)  )))))
 = 0 + 2 * (1 + 2 * (0 + 2 * (1 + 2 * 1 + f(b0 b0, 2) )))))
>>

For the sum to be correct, f(b0 b0, 2) must be zero.
But if we continue unrolling f with the pattern we saw, it IS zero :
<<
f(b0 b0, 2) = 0 + 2 * f(b0, 1)
            = 0 + 2 * (0 + 2 * 0 + (2 * f(nil, 0)))
            = 0 + 2 * (0 + 2 * 0 + (2 * 0)))
            = 0
>>

So it seems we're good with only clauses A and B.

-- What happens on trimmed vectors ?

For vec_of_N, we could give a big N to convert into a small vector,
such that the N is trimmed.
In our case, N_of_vec, the size of the vec equals the number of its elements,
by definition, so there is no such problem.

Looks like A and B do the job, let's implement it.

Remember :
<<
A: f(b :: bs, S w) = b + 2 * f(bs, w)
B: f(b, 0) = 0
>>
*)

Definition b2n (b : bit) : N :=
  match b with
  | b0 => 0%N
  | b1 => 1%N
  end.
 
Fixpoint N_of_vec (w : nat) (v : Vector.t bit w) : N :=
  match v with
  | Vector.nil _ => 0%N
  | Vector.cons _ b w' v' => b2n b + 2 * (N_of_vec w' v')
  end.

Theorem N_of_vec_sanity_26 :
  N_of_vec _
  ( cons _ b0 _ 
  ( cons _ b1 _ 
  ( cons _ b0 _ 
  ( cons _ b1 _ 
  ( cons _ b1 _ 
  ( nil _)))))) = 26%N.
Proof. reflexivity. Qed.

Theorem N_of_vec_sanity_26_ext :
  N_of_vec _
  ( cons _ b0 _ 
  ( cons _ b1 _ 
  ( cons _ b0 _ 
  ( cons _ b1 _ 
  ( cons _ b1 _ 
  ( cons _ b0 _ 
  ( cons _ b0 _ 
  ( nil _)))))))) = 26%N.
Proof. reflexivity. Qed.

Theorem N_of_vec_sanity_1 :
  N_of_vec _ ( cons _ b1 _ (nil _)) = 1%N.
Proof. reflexivity. Qed.

Theorem N_of_vec_sanity_0 :
  N_of_vec _ ( cons _ b0 _ (nil _)) = 0%N.
Proof. reflexivity. Qed.

Theorem N_of_vec_sanity_nil :
  N_of_vec _ (nil _) = 0%N.
Proof. reflexivity. Qed.


(** Now let's see how hard it is to prove the roundtrip *)

Theorem N_vec_roundtrip_v1 : forall w, forall v : Vector.t bit w,
  vec_of_N _ (N_of_vec _ v) = v.
Proof.
  intros.
  induction v.
  - simpl. reflexivity.
  - unfold N_of_vec.
  Print N_of_vec.
  Print vec_of_N.
Abort.
  

(** Here we're stuck with this goal :
<<
vec_of_N (S n) (N_of_vec (S n) (cons bit h n v)) = cons bit h n v
>>
let's draft on paper see if it's true or not :
We start from the left side, and try succesive rewrites until we reach the right side.

Lemma 1 :
(N_of_vec (S n) (cons bit h n v)) 
  = b2n h + 2 * N_of_vec n v

So  :

<<
left-side 
= vec_of_N (S n) (N_of_vec (S n) (cons bit h n v)) 
= vec_of_N (S n) (b2n h + 2 * N_of_vec n v) 
= vec_of_N (S n) (b2n h + 2 * N_of_vec n v) 
>>

We can't go further here, but notice a key truth that would help.
With a bit of boolean arithmetic, we can find out :

Lemma 2 :
<<
vec_of_N _ (b + 2 * v) = cons _ b (vec_of_N _ v)
>>

so :
<<
  vec_of_n (s n) (n_of_vec (s n) (cons bit h n v)) 
= vec_of_n (s n) (b2n h + 2 * n_of_vec n v)     (lemma 1)
= vec_of_n (s n) (b2n h + 2 * n_of_vec n v) 
= vec_of_n (s n) (b2n h + 2 * n_of_vec n v) 
= cons (h)  (vec_of_n _ (n_of_vec n v)          (lemma 2)
= cons (h)  (v)                                 (ih)
>>

And here we are !

With hindsight, we want to write a proof involving two functions,
and the prove can only go by induction.
But :
- N_of_vec  is 'linked' to its recursive call through a [cons] relationship.
- vec_of_N  is 'linked' to its recursive call through a [_ + 2 * _] relationship.

So, if we want to do induction on both,
we funamentally need a link between [cons] and [_ + 2 * _].
That's why we need those lemma.
*)


Lemma lemma1 : forall w, forall v : Vector.t bit w,
  forall b,
  N_of_vec _ (cons bit b _ v) = (b2n b) + (2%N * (N_of_vec _ v)).
Proof. reflexivity. Qed.

Lemma vec_z : forall w, (vec_of_pos w None) = (vec_zeroes w).
Proof. induction w; crush. Qed.

Lemma lemma2 : forall (w : nat) (b : bit) (n : N),
  vec_of_N (S w) ((b2n b) + 2 * n) = Vector.cons bit b w (vec_of_N w n).
Proof.
  destruct b; destruct n; simpl; auto.
  rewrite vec_z; reflexivity.
Qed.

Theorem N_vec_roundtrip_ : forall w, forall v : Vector.t bit w,
  vec_of_N _ (N_of_vec _ v) = v.
Proof.
  intros.
  induction v.
  - simpl. reflexivity.
  -
  
(**
Remember the outline of the proof :
<<
  vec_of_n (s n) (n_of_vec (s n) (cons bit h n v)) 
= vec_of_n (s n) (b2n h + 2 * n_of_vec n v)     (lemma 1)
= vec_of_n (s n) (b2n h + 2 * n_of_vec n v) 
= cons (h)  (vec_of_n _ (n_of_vec n v)          (lemma 2)
= cons (h)  (v)                                 (IH)
>>
*)
  rewrite lemma1.
  rewrite lemma2.
  rewrite IHv.
  reflexivity.
Qed.
 
(**
  Now the other way around, from N to vec and back.
  Let's outline the proof of N_of_vec _ (vec_of_N _ n) = n
  
  First, is it true ?
  [n] can encode any number up to infinity, but vec cannot, it's limited by its width.
  imagine encoding 255 to a 3-bit vector, you'll get [1; 1; 1],
  which coverts back to 7 (and not 255).
  In the roundtrip, the 'bits above the MSB' are lost.

  We should re-state the theorem to account for this.
  But how will we restate it ?
  Let's first try to write the inductive proof to see which rewrite will best suit the proof.


  N_of_vec _ (vec_of_N _ n)
= N_of_vec _ (vec_of_pos _ p)    // ignoring the N0 case here as it will be trivial.

We'll have 5 case to handle now, because of the 5 clauses in the [vec_of_pos] match statement.

---- case 1 - width 0

...
= N_of_vec _ (vec_of_pos 0 p)   
= N_of_vec _ (Vector.nil))   
= N_of_vec _ (Vector.nil))   
= 0%N
!= Npos p
As is, the statement is incorrect.
the roundtrip doesn't make us go back to [p] but to [0] here.

The truncation can be expressed as : p mod (2^w).
In this case, p mod (2^0) = p mod 1 = 0
This is a match !

We can add [N < 2^w] as a general precondition to our theorem.
In this case (width 0), the precondition will become :
[N < 2^0] i.e. [N < 1] i.e. [N = 0] i.e. [Npos p = 0]
Which will bring our missing equality above !

Precond : [N < 2 ^ w]

---- case 2 - p = None

left
...
= N_of_vec (S w') (vec_of_pos (S w') None)   
= N_of_vec _ (vec_of_pos (S w') None)   
= N_of_vec _ ( Vector.cons b0 _ (vec_of_pos w' None]) )    // eval vec_of_pos
= (b2n b0) + 2 * (N_of_vec (vec_of_pos w' None))           // eval N_of_vec
= 2 * (N_of_vec _ (vec_of_pos w' None))                    // 0 + x = x
= 2 * p                                                    // IH 
!= p

How come we get stuck here ?
The intuition is that, at this point of the recursion on [vec_of_pos],
the rest of the vector to convert is all zeroes, so the mutliplication by 2 doesn't break the equality.
But how to convey this in the proof ?

Well, let's go back and see how vec_of_pos will appear in our proof.
It is called by [vec_of_N], and if we go back to its definition...
we see that we always call [vec_of_pos] with [Some p],
so the [None] case won't ever appear in our proof.

so let's skip this non-existent case and go to case 3.

---- case 3 : p = xH

There's no IH since p = xH here, there's no inner [p'].

left
= N_of_vec (S w') (vec_of_pos (S w') (Some xH))   
= N_of_vec (S w') (Vector.cons _ b1 w' (vec_of_pos w' None))      // unfold vec_of_pos
= (b1n b1) + 2 * ( N_of_vec w' (vec_of_pos w' None))              // unfold N_of_vec
= (b1n b1) + 2 * ( N_of_vec w' (vec_zeroes w' ))                  // apply vec_z
= (b1n b1) + 2 * ( N_of_vec w' (vec_zeroes w' ))                  // apply some easy lemma [n_of_zeroes]
= 1%N      + 2 * 0%N
= 1%N
= Npos (xH)
= Npos (p)
QED !

---- case 4 : p = x0 p'

IH : N_of_vec _ (vec_of_pos _ (Some p')) = Npos p'

left
= N_of_vec (S w') (vec_of_pos (S w') (Some x0 p'))   
= N_of_vec (S w') (Vector.cons _ b0 w' (vec_of_pos (Some p')))   // eval vec_of_pos
= (b2n b0) w' + 2 * (N_of_vec (vec_of_pos (Some p')))            // eval vec_of_pos
= 0%N + 2 * (Npos p')                                            // IH
= 2 * (Npos p')                                                  // 0 + x = x
= Npos (x0 p')                                                   // some trivial unnamed lemma 
= Npos p
QED

---- case 5 : p = x1 p'

It will go almost exactly the same as case 4, except at the end,
where the trivial unnamed lemma won't be [2 * (Npos p) = Npos (x0 p)],
but rather [1 + 2 * (Npos p) = Npos (x1 p)] :

...
= 1%N + 2 * (Npos p')                                            // IH
= 1 + 2 * (Npos p')                                              // 0 + x = x
= Npos (x1 p')                                                   // some other trivial unnamed lemma 
= Npos p
QED

*)

(**
We can start with the little lemma :
*)

Lemma n_of_zeroes : forall w, N_of_vec w (vec_zeroes w) = 0%N.
Proof.
  induction w; simpl; try rewrite IHw; reflexivity.
Qed.


Require Import Lia.









Lemma annoying_precond_xO : forall p w,
  N.pos (xO p) < 2 ^ N.of_nat (S w) -> N.pos p < 2 ^ (N.of_nat w).
Proof.
  intros.

  assert (Hrw : N.pos p~0 = 2 * (N.pos p)).
  { nia. }
  rewrite Hrw in H. clear Hrw.

  assert (Hrw : forall x, N.succ (N.of_nat x) = N.of_nat (S x)).
  { intro. nia. }
  rewrite <- (Hrw w) in H. clear Hrw.

  assert (Hrw : 2 ^ N.succ (N.of_nat w) = 2 * (2 ^ N.of_nat w)).
  { rewrite <- N.pow_succ_r.
    - reflexivity.
    - lia.
  }
  rewrite Hrw in H. clear Hrw.

  assert (Hrw : forall n m : N, 2 * n < 2 * m -> n < m).
  { nia. }
  apply Hrw in H.

  assumption.
Qed.


Lemma annoying_precond_xI : forall p w,
  N.pos (xI p) < 2 ^ N.of_nat (S w) -> N.pos p < 2 ^ (N.of_nat w).
Proof.
  intros.
  apply annoying_precond_xO.
  apply N.le_lt_trans with (m := N.pos p~1).
  - nia.
  - assumption.
Qed.



Lemma vec_N_roundtrip_0 : forall w, N_of_vec w (vec_of_N w 0) = 0.
Proof.
  induction w.
  - simpl. reflexivity.
  - simpl in IHw.
  simpl.
  rewrite IHw.
  reflexivity.
Qed.

Theorem vec_N_roundtrip :
  forall (w : nat)
         (n : N)
         (Htrunc : n < 2%N ^ (N.of_nat w)),
  N_of_vec w (vec_of_N w n) = n.
Proof.
  intros.
  destruct n.
  (* N = 0*)
  { simpl. apply n_of_zeroes. }
  (* N = Npos p *)
  {
    (* destruct w eqn:Hw.
    (* case 1 : w = 0 *)
    { simpl. destruct p; try inversion Htrunc; try reflexivity. }
   *)
    (* other cases (w = S w') *)

    (* We need an IH forall w, otherwise we won't be able to apply it later,
    because the too struct IH will be true for [S w'] only, and we'll need it for [w'] *)
    generalize dependent w.
    induction p.

    - (* p = xI p' *)
      destruct w eqn:Hw.
      { simpl. intro Hcontra. inversion Hcontra. }
      { rename n into w'.
      (* Turns out there will be a bit of N-arith to do to make our IH truly available *)

      unfold vec_of_N.

        assert (Hrw1: vec_of_pos (S w') (Some (p~1)%positive) = 
          Vector.cons _ b1 w' (vec_of_pos w' (Some p%positive))).
        { simpl. reflexivity. }
        rewrite Hrw1.

        assert (Hrw2: forall b,
             N_of_vec (S w') (cons bit b w' (vec_of_pos w' (Some p)))
          = (b2n b) + 2 * (N_of_vec w' (vec_of_pos w' (Some p)))).
        { destruct b; reflexivity. }

        rewrite Hrw2.

        assert (Hrw3 : vec_of_N (S w') (N.pos p) = vec_of_pos (S w') (Some p)).
        { reflexivity. }


        intro Hle.
        rewrite IHp.
        { (* main proof continuing *)
          simpl. reflexivity.
        }

        (* The main proof is done,
        now we need this annoying precondition to pass :
        xI p < 2 ^ (w + 1) ->
        p    < 2 ^ w
        *)
        Check annoying_precond_xI.
        apply annoying_precond_xI.
        assumption.
      }

  - (* p = xO p' *)
      destruct w eqn:Hw.
      { simpl. intro Hcontra. inversion Hcontra. }
      { rename n into w'.
      (* Turns out there will be a bit of N-arith to do to make our IH truly available *)

      unfold vec_of_N.

        assert (Hrw1: vec_of_pos (S w') (Some (p~0)%positive) = 
          Vector.cons _ b0 w' (vec_of_pos w' (Some p%positive))).
        { simpl. reflexivity. }
        rewrite Hrw1.

        assert (Hrw2: forall b,
             N_of_vec (S w') (cons bit b w' (vec_of_pos w' (Some p)))
          = (b2n b) + 2 * (N_of_vec w' (vec_of_pos w' (Some p)))).
        { destruct b; reflexivity. }

        rewrite Hrw2.

        assert (Hrw3 : vec_of_N (S w') (N.pos p) = vec_of_pos (S w') (Some p)).
        { reflexivity. }


        intro Hle.
        rewrite IHp.
        { (* main proof continuing *)
          simpl. reflexivity.
        }

        (* The main proof is done,
        now we need this annoying precondition to pass :
        xI p < 2 ^ (w + 1) ->
        p    < 2 ^ w
        *)
        apply annoying_precond_xO.
        assumption.
      }

      - (* p = xH *)
      intros.
      induction w.
      + inversion Htrunc.
      + { 
        Check Vector.cons.

        assert (Hrw : vec_of_N (S w) 1 = Vector.cons _ b1 w (vec_of_N w 0)).
        { simpl. rewrite vec_z. reflexivity. }
        rewrite Hrw. clear Hrw.

        assert (Hrw : forall b w v, N_of_vec (S w) (cons _ b w v)
         = (b2n b) + 2 * (N_of_vec w v)).
        { auto. } 
        rewrite Hrw. clear Hrw.

        rewrite vec_N_roundtrip_0.
        simpl.
        reflexivity.
      }
  }

Qed.



