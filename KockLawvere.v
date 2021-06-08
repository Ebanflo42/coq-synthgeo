Require Import Setoid.

(* The basic structure of the Kock-Lawvere real numbers *)
(* There is some redundancy in these axioms, for convenience *)
Record KockLawvere :=
{ synthreal : Prop

(* Addition forms an Abelian group *)
; zero : synthreal
; add : synthreal -> synthreal -> synthreal
; add_id : forall (x : synthreal), add x zero = x
; add_assoc : forall (x y z : synthreal), add (add x y) z = add x (add y z)
; add_comm : forall (x y : synthreal), add x y = add y x
; add_inv : forall (x : synthreal),
  (exists (negx : synthreal),add x negx = zero)

(* Multiplication forms a commutative monoid with inverses except at 0 *)
; one : synthreal
; mul : synthreal -> synthreal -> synthreal
; mul_id : forall (x : synthreal), mul x one = x
; mul_assoc : forall (x y z : synthreal), mul (mul x y) z = mul x (mul y z)
; mul_comm : forall (x y : synthreal), mul x y = mul y x
; mul_inv : forall (x : synthreal), x <> zero
  -> (exists (invx : synthreal), mul x invx = one)

(* Multiplication distributes over addition *)
; left_distrib : forall (x y z : synthreal),
  mul x (add y z) = add (mul x y) (mul x z)
; right_distrib : forall (x y z : synthreal),
  mul (add x y) z = add (mul x z) (mul y z)

(* A total ordering which behaves nicely with the field operations *)
; lessthan : synthreal -> synthreal -> Prop
; transitive : forall (x y z : synthreal), (lessthan x y) -> (lessthan y z)
  -> (lessthan x z)
; zero_less_one : lessthan zero one
; total : forall (x y : synthreal), x <> y -> lessthan x y \/ lessthan y x
; translation : forall(x y z : synthreal),
  lessthan x y -> lessthan (add x z) (add y z)
; dilation : forall (x y z : synthreal),
  (not (lessthan z zero) /\ lessthan x y) -> lessthan (mul z x) (mul z y)

(* Square roots existence and uniqueness *)
; sqrt_exist : forall (x : synthreal), (exists (y : synthreal), mul y y = x)
; sqrt_uniq : forall (x y : synthreal), (lessthan zero y /\ mul y y = x)
  -> y = ex_proj1 (sqrt_exist x)

(* Nilsquare infinitesimals are treated as a separate type *)
(* with an injection into the rest of the field *)
; nilsquares : Prop
; nilsquare_incl : nilsquares -> synthreal
; nilsquare_subset : forall (d1 d2 : nilsquares),
  nilsquare_incl d1 = nilsquare_incl d2 -> d1 = d2
; nilsquare_def : forall (d : nilsquares),
  mul (nilsquare_incl d) (nilsquare_incl d) = zero
; nilsquare_recl : forall (x : synthreal),
  forall (nilsqr : mul x x = zero), exists (d : nilsquares), x = nilsquare_incl d
; nilzero : nilsquares
; nilzero_def : nilsquare_incl nilzero = zero

(* The Kock-Lawvere axioms! *)
; linearization_exist : forall (f : nilsquares -> synthreal),
  (exists (a : synthreal), forall (d : nilsquares), 
    f d = add (f nilzero) (mul a (nilsquare_incl d)))
; linearization_uniq : forall (f : nilsquares -> synthreal),
  forall (a : synthreal), (forall (d : nilsquares),
    f d = add (f nilzero) (mul a (nilsquare_incl d)))
      -> a = ex_proj1 (linearization_exist f)

}.


(* Basic algebra stuff *)


Fact cancel_add : forall (K: KockLawvere),
  forall (x y z : synthreal K),
  add K x z = add K y z -> x = y.
Proof.
intros K x y z hyp.
rewrite <- (add_id K x).
destruct (add_inv K z).
rewrite <- H.
rewrite <- (add_assoc K x z x0).
rewrite -> hyp.
rewrite -> (add_assoc K y z x0).
rewrite -> H.
rewrite -> (add_id K y).
reflexivity.
Qed.


Fact mul_zero : forall (K : KockLawvere),
  forall (x : synthreal K),
  mul K (zero K) x = zero K.
Proof.
intros K x.
assert (add K (mul K (zero K) x) (mul K (zero K) x)
  = add K (zero K) (mul K (zero K) x)).
rewrite -> (add_comm K (zero K) (mul K (zero K) x)).
rewrite -> (add_id K).
rewrite <- (right_distrib K (zero K) (zero K) x).
rewrite -> (add_id K (zero K)) at 1.
reflexivity.
exact (cancel_add K (mul K (zero K) x) (zero K) (mul K (zero K) x) H).
Qed.


(* A few utilities before beginning single variable calculus *)


Definition diff (K : KockLawvere) (x : synthreal K)
  (d : nilsquares K) : synthreal K := mul K (nilsquare_incl K d) x.


Fact nilsquare_diff : forall (K : KockLawvere),
  forall (x : synthreal K),
  forall (d : nilsquares K),
  mul K (diff K x d) (diff K x d) = zero K.
Proof.
intros K x d.
unfold diff.
rewrite -> (mul_comm K (nilsquare_incl K d) x) at 1.
rewrite -> (mul_assoc K x (nilsquare_incl K d) (mul K (nilsquare_incl K d) x)).
rewrite <- (mul_assoc K (nilsquare_incl K d) (nilsquare_incl K d) x).
rewrite -> (nilsquare_def K d).
rewrite -> (mul_zero K).
rewrite -> (mul_comm K).
rewrite -> (mul_zero K).
reflexivity.
Qed.


Fact linearize_diff : forall (K : KockLawvere),
  forall (x : synthreal K),
  ex_proj1 (linearization_exist K (diff K x)) = x.
Proof.
intros K x.
assert (forall (d : nilsquares K),
  diff K x d = add K (diff K x (nilzero K)) (mul K x (nilsquare_incl K d))).
intros d.
unfold diff.
rewrite -> (nilzero_def K).
rewrite -> (mul_zero K).
rewrite -> (add_comm K).
rewrite -> (add_id K).
rewrite -> (mul_comm K).
reflexivity.
symmetry.
exact (linearization_uniq K (diff K x) x H).
Qed.


Lemma microcancellation : forall (K : KockLawvere),
  forall (x y : synthreal K),
  diff K x = diff K y -> x = y.
Proof.
intros K x y hyp.
rewrite <- (linearize_diff K x).
rewrite <- (linearize_diff K y).
rewrite -> hyp.
reflexivity.
Qed.


(* Single-variable calculus! *)


Definition derivative (K : KockLawvere)
  (f : synthreal K -> synthreal K)
  (x : synthreal K) : synthreal K :=
  ex_proj1 (linearization_exist K (fun d => f (add K x (nilsquare_incl K d)))).


Theorem product_rule : forall (K : KockLawvere),
  forall (f : synthreal K -> synthreal K),
  forall (g : synthreal K -> synthreal K),
  forall (x : synthreal K),
  derivative K (fun y => mul K (f y) (g y)) x
  = add K (mul K (derivative K f x) (g x)) (mul K (f x) (derivative K g x)).
Proof.
intros K f g x.
unfold derivative at 1.
fold (derivative K f).


Theorem derivative_distrib : forall (K : KockLawvere),
  forall (f : synthreal K -> synthreal K),
  forall (g : synthreal K -> synthreal K),
  forall (x : synthreal K),
  add K (derivative K f x) (derivative K g x)
  = derivative K (fun y => add K (f y) (g x)) x.
Proof.
intros K f g x.
unfold derivative.