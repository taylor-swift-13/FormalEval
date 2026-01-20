Require Import ZArith.
Require Import Zdiv.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example modp_test : modp_spec 3%Z 3%Z 2%Z.
Proof.
  unfold modp_spec.
  split.
  - lia.
  - reflexivity.
Qed.