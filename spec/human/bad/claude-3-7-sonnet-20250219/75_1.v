Require Import Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.micromega.Lia.

Open Scope Z_scope.

Definition problem_75_pre (a : Z) : Prop := a < 100.

Definition problem_75_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ a = p1 * p2 * p3).

Example problem_75_test_5 :
  problem_75_pre 5 ->
  problem_75_spec 5 false.
Proof.
  intros Hpre.
  unfold problem_75_spec.
  split.
  - intros Hb. subst.
    (* Hb : true = true, so exists p1 p2 p3 ... *)
    destruct Hb as [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Ha]]]]]].
    (* Each prime >= 2 *)
    assert (H2p1 : 2 <= p1) by (apply prime_ge_2; auto).
    assert (H2p2 : 2 <= p2) by (apply prime_ge_2; auto).
    assert (H2p3 : 2 <= p3) by (apply prime_ge_2; auto).
    (* So product >= 8 > 5, contradiction *)
    lia.
  - intros [p1 [p2 [p3 [Hp1 [Hp2 [Hp3 Ha]]]]]].
    (* From primes >= 2, product >= 8 *)
    assert (H2p1 : 2 <= p1) by (apply prime_ge_2; auto).
    assert (H2p2 : 2 <= p2) by (apply prime_ge_2; auto).
    assert (H2p3 : 2 <= p3) by (apply prime_ge_2; auto).
    assert (Hprod : 8 <= p1 * p2 * p3).
    { apply Z.mul_le_mono_nonneg; lia. }
    rewrite Ha in Hprod.
    lia.
Qed.