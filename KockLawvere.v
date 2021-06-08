Require Import Setoid.

Record KockLawvere :=
{ synthreal : Prop

; zero : synthreal
; add : synthreal -> synthreal -> synthreal
; add_id : forall (x : synthreal), add x zero = x
; add_assoc : forall (x y z : synthreal), add (add x y) z = add x (add y z)
; add_comm : forall (x y : synthreal), add x y = add y x
; add_inv : forall (x : synthreal),
  (exists (negx : synthreal),add x negx = zero)

; one : synthreal
; mul : synthreal -> synthreal -> synthreal
; mul_id : forall (x : synthreal), mul x one = x
; mul_assoc : forall (x y z : synthreal), mul (mul x y) z = mul x (mul y z)
; mul_comm : forall (x y : synthreal), mul x y = mul y x
; mul_inv : forall (x : synthreal), x <> zero
  -> (exists (invx : synthreal), mul x invx = one)

; left_distrib : forall (x y z : synthreal),
  mul x (add y z) = add (mul x y) (mul x z)
; right_distrib : forall (x y z : synthreal),
  mul (add x y) z = add (mul x z) (mul y z)

; lessthan : synthreal -> synthreal -> Prop
; transitive : forall (x y z : synthreal), (lessthan x y) -> (lessthan y z)
  -> (lessthan x z)
; zero_less_one : lessthan zero one
; total : forall (x y : synthreal), x <> y -> lessthan x y \/ lessthan y x
; translation : forall(x y z : synthreal),
  lessthan x y -> lessthan (add x z) (add y z)
; dilation : forall (x y z : synthreal),
  (not (lessthan z zero) /\ lessthan x y) -> lessthan (mul z x) (mul z y)

; sqr_exist : forall (x : synthreal), (exists (y : synthreal), mul y y = x)
; sqr_uniq : forall (x y : synthreal), (lessthan zero y /\ mul y y = x)
  -> y = ex_proj1 (sqr_exist x)

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

; linearization_exist : forall (f : nilsquares -> synthreal),
  (exists (a : synthreal), forall (d : nilsquares), 
    f d = add (f nilzero) (mul a (nilsquare_incl d)))
; linearization_uniq : forall (f : nilsquares -> synthreal),
  forall (a : synthreal), (forall (d : nilsquares),
    f d = add (f nilzero) (mul a (nilsquare_incl d)))
      -> a = ex_proj1 (linearization_exist f)

}.

Definition diff (K : KockLawvere) (x : synthreal K) (d : nilsquares K) : synthreal K :=
  mul K (nilsquare_incl K d) x.

Lemma cancel_add : forall (K: KockLawvere), forall (x y z : synthreal K), add K x z = add K y z -> x = y.
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

Lemma mul_zero : forall (K : KockLawvere), forall (x : synthreal K), mul K (zero K) x = zero K.
Proof.
intros K x.
assert (mul K (zero K) x = add K (mul K (zero K) x) (mul K (zero K) x)).
rewrite <- (add_id K (zero K)) at 1.
rewrite -> (right_distrib K (zero K) (zero K) x).
reflexivity.
rewrite -> H.

Lemma nilsquare_diff : forall (K : KockLawvere), forall (x : synthreal K), forall (d : nilsquares K),
  mul K (diff K x d) (diff K x d) = zero K.
Proof.
intros K x d.
unfold diff.
rewrite -> (mul_comm K (nilsquare_incl K d) x) at 1.
rewrite -> (mul_assoc K x (nilsquare_incl K d) (mul K (nilsquare_incl K d) x)).

Lemma linearize_diff : forall (K : KockLawvere), forall (x : synthreal K),
  ex_proj1 (linearization_exist K (diff K x)) = x.
Proof.
intros K x.

Lemma microcancellation : forall (K : KockLawvere), forall (x y : synthreal K),
  forall (d : nilsquares K),
    mul K (nilsquare_incl K d) x = mul K (nilsquare_incl K d) y -> x = y.
Proof.
intros K x y d hyp.
Goal ex_proj1 (linearization_exists K (fun d1 => mul K (nilsquare incl K d1) x)) = x.