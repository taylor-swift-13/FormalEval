Require Import Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory. (* Contains definition of prime *)
Require Import Coq.micromega.Psatz.   (* Contains nia tactic for non-linear arithmetic *)
Open Scope Z_scope.

Definition problem_75_pre (a : Z) : Prop := a < 100.

Definition problem_75_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ a = p1 * p2 * p3).

Example test_case : problem_75_spec 21 false.
Proof.
  unfold problem_75_spec.
  split.
  - intros H.
    inversion H.
  - intros (p1 & p2 & p3 & Hp1 & Hp2 & Hp3 & Heq).
    apply prime_ge_2 in Hp1.
    apply prime_ge_2 in Hp2.
    apply prime_ge_2 in Hp3.
    assert (p1 >= 3).
    { destruct (Z.eq_dec p1 2).
      - subst. nia.
      - nia. }
    assert (p2 >= 3).
    { destruct (Z.eq_dec p2 2).
      - subst. nia.
      - nia. }
    assert (p3 >= 3).
    { destruct (Z.eq_dec p3 2).
      - subst. nia.
      - nia. }
    nia.
Qed.