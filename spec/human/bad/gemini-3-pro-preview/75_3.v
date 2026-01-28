Require Import Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory. (* Contains definition of prime *)
Require Import Coq.micromega.Psatz.   (* Contains nia tactic for non-linear arithmetic *)
Open Scope Z_scope.

Definition problem_75_pre (a : Z) : Prop := a < 100.

Definition problem_75_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ a = p1 * p2 * p3).

Example test_case : problem_75_spec 8 true.
Proof.
  unfold problem_75_spec.
  split.
  - intros _.
    exists 2, 2, 2.
    repeat split.
    + apply prime_2.
    + apply prime_2.
    + apply prime_2.
    + reflexivity.
  - intros _.
    reflexivity.
Qed.