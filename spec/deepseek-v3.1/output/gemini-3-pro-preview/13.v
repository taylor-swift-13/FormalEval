Require Import ZArith.
Require Import Znumtheory.
Require Import Psatz.

Open Scope Z_scope.

Definition gcd_spec (a : Z) (b : Z) (result : Z) : Prop :=
  Zis_gcd a b result /\ result >= 0.

Example test_gcd_3_7 : gcd_spec 3 7 1.
Proof.
  unfold gcd_spec.
  split.
  - (* The error in the previous attempt was using Z.gcd_is_gcd (which doesn't exist) 
       instead of Zgcd_is_gcd (which is in Znumtheory). *)
    (* We replace 1 with the computed value of Z.gcd 3 7 *)
    replace 1 with (Z.gcd 3 7) by reflexivity.
    (* Apply the correctness lemma for Z.gcd *)
    apply Zgcd_is_gcd.
  - (* Prove 1 >= 0 *)
    lia.
Qed.