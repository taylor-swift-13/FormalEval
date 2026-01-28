Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_111111112_987654319 : gcd_spec 111111112 987654319 1.
Proof.
  unfold gcd_spec.
  split.
  - (* We replace 1 with the computed value of Z.gcd 111111112 987654319 *)
    replace 1 with (Z.gcd 111111112 987654319) by reflexivity.
    (* Apply the correctness lemma for Z.gcd *)
    apply Zgcd_is_gcd.
  - (* Prove 1 >= 0 *)
    lia.
Qed.