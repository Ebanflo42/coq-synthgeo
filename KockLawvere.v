Require Import Setoid.
Require Import FunctionalExtensionality.


Lemma uniq_choice : forall (A B : Prop),
  forall (P : A -> B -> Prop),
  (forall (a : A), exists! (b : B), P a b)
  -> (exists (f : A -> B), forall (a : A), P a (f a)).
Proof.
  intros.
  exists (fun a => ex_proj1 (H a)).
  intros.
  destruct (H a), u.
  auto.
Qed.


(**)
Record MRE :=
{ set : Prop
; elem : set
; op : set -> set -> set
; subset : Prop
; subset_incl : subset -> set
; exist_axiom : forall (f : subset -> set), exists! (x : set),
  f = fun y => op (subset_incl y) x
}.

Definition witness_fcn : forall (M : MRE),
  forall (f : set M -> set M),
  exists (fn : set M -> set M),
  forall (x : set M),
  (fun y => f (op M (subset_incl M y) x))
  = (fun y => op M (subset_incl M y) (fn x)).
Proof.
  intros.
  assert (forall (x : set M), exists! (y : set M),
    (fun d => f (op M (subset_incl M d) x))
    = (fun d => op M (subset_incl M d) y)).
  intro.
  exact (exist_axiom M (fun d => f (op M (subset_incl M d) x))).
  pose (pred := fun x => fun y =>
    (fun d : subset M => f (op M (subset_incl M d) x))
    = (fun d : subset M => op M (subset_incl M d) y)).
  exact (uniq_choice (set M ) (set M) pred H).
Defined.

(* The basic structure of the Rock-Lawvere real numbers *)
(* There is some redundancy in these axioms, for convenience *)
Record SynthReal :=
{ set : Prop

(* Addition forms an Abelian group *)
; zero : set
; add : set -> set -> set
; add_id : forall (x : set), add x zero = x
; add_assoc : forall (x y z : set), add (add x y) z = add x (add y z)
; add_comm : forall (x y : set), add x y = add y x
; add_inv : forall (x : set),
  (exists (negx : set), add x negx = zero)

(* Multiplication forms a commutative monoid with inverses except at 0 *)
; one : set
; mul : set -> set -> set
; mul_id : forall (x : set), mul x one = x
; mul_assoc : forall (x y z : set), mul (mul x y) z = mul x (mul y z)
; mul_comm : forall (x y : set), mul x y = mul y x
; mul_inv : forall (x : set), x <> zero
  -> (exists (invx : set), mul x invx = one)

(* Multiplication distributes over addition *)
; left_distrib : forall (x y z : set),
  mul x (add y z) = add (mul x y) (mul x z)
; right_distrib : forall (x y z : set),
  mul (add x y) z = add (mul x z) (mul y z)

(* A total ordering which behaves nicely with the field operations *)
; lessthan : set -> set -> Prop
; transitive : forall (x y z : set), (lessthan x y) -> (lessthan y z)
  -> (lessthan x z)
; zero_less_one : lessthan zero one
; total : forall (x y : set), x <> y -> lessthan x y \/ lessthan y x
; translation : forall(x y z : set),
  lessthan x y -> lessthan (add x z) (add y z)
; dilation : forall (x y z : set),
  (not (lessthan z zero) /\ lessthan x y) -> lessthan (mul z x) (mul z y)

(* Square roots existence and uniqueness *)
; sqrt_exist : forall (x : set), (exists (y : set), mul y y = x)
; sqrt_uniq : forall (x y : set), (lessthan zero y /\ mul y y = x)
  -> y = ex_proj1 (sqrt_exist x)

(* Nilsquare infinitesimals are treated as a separate type *)
(* with an injection into the rest of the field *)
; nilsquares : Prop
; nilsquare_incl : nilsquares -> set
; nilsquare_subset : forall (d1 d2 : nilsquares),
  nilsquare_incl d1 = nilsquare_incl d2 -> d1 = d2
; nilsquare_def : forall (d : nilsquares),
  mul (nilsquare_incl d) (nilsquare_incl d) = zero
; nilsquare_recl : forall (x : set),
  forall (nilsqr : mul x x = zero),
    exists (d : nilsquares), x = nilsquare_incl d
; nilzero : nilsquares
; nilzero_def : nilsquare_incl nilzero = zero

(* The Kock-Lawvere axiom! *)
; KockLawvere : forall (f : nilsquares -> set),
  (exists (a : set),
    f = fun d => add (f nilzero) (mul a (nilsquare_incl d)))

}.


(* Basic algebra stuff *)


Fact cancel_add : forall (R: SynthReal),
  forall (x y z : set R),
  add R x z = add R y z -> x = y.
Proof.
intros R x y z hyp.
rewrite <- (add_id R x).
destruct (add_inv R z).
rewrite <- H.
rewrite <- (add_assoc R x z x0).
rewrite -> hyp.
rewrite -> (add_assoc R y z x0).
rewrite -> H.
rewrite -> (add_id R y).
reflexivity.
Qed.


Fact mul_zero : forall (R : SynthReal),
  forall (x : set R),
  mul R (zero R) x = zero R.
Proof.
intros R x.
assert (add R (mul R (zero R) x) (mul R (zero R) x)
  = add R (zero R) (mul R (zero R) x)).
rewrite -> (add_comm R (zero R) (mul R (zero R) x)).
rewrite -> (add_id R).
rewrite <- (right_distrib R (zero R) (zero R) x).
rewrite -> (add_id R (zero R)) at 1.
reflexivity.
exact (cancel_add R (mul R (zero R) x) (zero R) (mul R (zero R) x) H).
Qed.


(* A few utilities before beginning single variable calculus *)


Definition diff (R : SynthReal) (x : set R)
  (d : nilsquares R) : set R := mul R (nilsquare_incl R d) x.


Fact nilsquare_diff : forall (R : SynthReal),
  forall (x : set R),
  forall (d : nilsquares R),
  mul R (diff R x d) (diff R x d) = zero R.
Proof.
intros R x d.
unfold diff.
rewrite -> (mul_comm R (nilsquare_incl R d) x) at 1.
rewrite -> (mul_assoc R x (nilsquare_incl R d) (mul R (nilsquare_incl R d) x)).
rewrite <- (mul_assoc R (nilsquare_incl R d) (nilsquare_incl R d) x).
rewrite -> (nilsquare_def R d).
rewrite -> (mul_zero R).
rewrite -> (mul_comm R).
rewrite -> (mul_zero R).
reflexivity.
Qed.


Fact linearize_diff : forall (R : SynthReal),
  forall (x : set R),
  ex_proj1 (linear_exist R (diff R x)) = x.
Proof.
intros R x.
assert (forall (d : nilsquares R),
  diff R x d = add R (diff R x (nilzero R)) (mul R x (nilsquare_incl R d))).
intros d.
unfold diff.
rewrite -> (nilzero_def R).
rewrite -> (mul_zero R).
rewrite -> (add_comm R).
rewrite -> (add_id R).
rewrite -> (mul_comm R).
reflexivity.
symmetry.
exact (linear_uniq R (diff R x) x H).
Qed.


Lemma microcancellation : forall (R : SynthReal),
  forall (x y : set R),
  diff R x = diff R y -> x = y.
Proof.
intros R x y hyp.
rewrite <- (linearize_diff R x).
rewrite <- (linearize_diff R y).
rewrite -> hyp.
reflexivity.
Qed.


(* Single-variable calculus! *)

(**)
Remark derivative_w_prf : forall (R : SynthReal),
  forall (f : set R -> set R),
  exists (df : set R -> set R),
  forall (x : set R),
  forall (d : nilsquares R),
  f (add R x (nilsquare_incl R d))
  = add R (f x) (mul R (nilsquare_incl R d) (df x)).
Proof.
intros R f.
pose (df0 := fun x =>
  (linear_exist R (fun d => (f (add R x (nilsquare_incl R d)))))).
exists (fun x => ex_proj1 (df0 x)).
intros x d.
(**)


Definition derivative (R : SynthReal)
  (f : set R -> set R)
  (x : set R) : set R :=
  ex_proj1 (linear_exist R (fun d => f (add R x (nilsquare_incl R d)))).


Fact rewrite_derivative : forall (R : SynthReal),
  forall (f : set R -> set R),
  forall (x : set R),
  forall (d : nilsquares R),
  f (add R x (nilsquare_incl R d))
  = add R (f x) (mul R (nilsquare_incl R d) (derivative R f x)).
Proof.
intros R f x d.
pose (ex_df := fun y =>
  linear_exist R (fun d0 => f (add R y (nilsquare_incl R d0)))).
unfold derivative.
exact (linear_uniq R (fun d1 =>
  f (add R x (nilsquare_incl R d1))) (derivative R f x) H).


Proposition product_rule : forall (R : SynthReal),
  forall (f : set R -> set R),
  forall (g : set R -> set R),
  forall (x : set R),
  derivative R (fun y => mul R (f y) (g y)) x
  = add R (mul R (derivative R f x) (g x)) (mul R (f x) (derivative R g x)).
Proof.
intros R f g x.
unfold derivative at 1.
fold (derivative R f).


Theorem derivative_distrib : forall (R : SynthReal),
  forall (f : set R -> set R),
  forall (g : set R -> set R),
  forall (x : set R),
  add R (derivative R f x) (derivative R g x)
  = derivative R (fun y => add R (f y) (g x)) x.
Proof.
intros R f g x.
unfold derivative.