Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.

Definition fib_spec (n : nat) (fib_n : nat) : Prop :=
  (n = 0 -> fib_n = 0) /\
  (n = 1 \/ n = 2 -> fib_n = 1) /\
  (n >= 3 -> exists a b, 
    a = 1 /\ b = 1 /\ 
    (forall i, 3 <= i <= n -> exists a_i b_i, 
      a_i = b /\ b_i = a + b /\ a = a_i /\ b = b_i) /\ 
    fib_n = b).

Lemma fib_spec_implies_n_lt_3: forall n f, fib_spec n f -> n < 3.
Proof.
  intros n f Hspec.
  destruct Hspec as [Hz [H12 Hge3]].
  assert (~ 3 <= n) as Hnot.
  { intros Hge.
    specialize (Hge3 Hge) as [a [b [Ha1 [Hb1 [Hall _]]]]].
    specialize (Hall 3).
    assert (3 <= 3 <= n) by lia.
    specialize (Hall H) as [a3 [b3 [Ha3b [Hb3ab [Ha_eq Hb_eq]]]]].
    (* From b = b3 and b3 = a + b, get b = a + b *)
    pose proof (eq_trans Hb_eq Hb3ab) as Hsum.
    (* Turn into a + b = 0 + b and cancel right *)
    pose proof (eq_sym Hsum) as Hsum'.
    rewrite <- Nat.add_0_l in Hsum'.
    apply (Nat.add_cancel_r a 0 b) in Hsum'.
    rewrite Ha1 in Hsum'. lia.
  }
  lia.
Qed.

Example fib_test_10_55_nat : ~ fib_spec 10%nat 55%nat.
Proof.
  intros Hspec.
  pose proof (fib_spec_implies_n_lt_3 10%nat 55%nat Hspec) as Hlt.
  lia.
Qed.

Example fib_test_input_output : ~ fib_spec (Z.to_nat 10%Z) (Z.to_nat 55%Z).
Proof.
  simpl.
  intros Hspec.
  eapply fib_spec_implies_n_lt_3 in Hspec.
  lia.
Qed.