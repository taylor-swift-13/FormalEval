Require Import Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory. (* Contains definition of prime *)
Require Import Coq.micromega.Psatz.   (* Contains nia tactic for non-linear arithmetic *)
Open Scope Z_scope.

Definition problem_75_pre (a : Z) : Prop := a < 100.

Definition problem_75_spec (a : Z) (b : bool) : Prop :=
  (b = true <-> exists p1 p2 p3, prime p1 /\ prime p2 /\ prime p3 /\ a = p1 * p2 * p3).

Example test_case : problem_75_spec (-2) false.
Proof.
  unfold problem_75_spec.
  split.
  - (* direction: false = true -> exists ... *)
    intros H.
    inversion H.
  - (* direction: exists ... -> false = true *)
    intros (p1 & p2 & p3 & Hp1 & Hp2 & Hp3 & Heq).
    (* In Coq's Znumtheory, prime p implies p >= 2 *)
    apply prime_ge_2 in Hp1.
    apply prime_ge_2 in Hp2.
    apply prime_ge_2 in Hp3.
    (* If p1, p2, p3 >= 2, then p1 * p2 * p3 >= 8 *)
    (* However, Heq states -2 = p1 * p2 * p3, which creates a contradiction (-2 >= 8) *)
    (* nia (Non-linear Integer Arithmetic) solves this contradiction automatically *)
    nia.
Qed.