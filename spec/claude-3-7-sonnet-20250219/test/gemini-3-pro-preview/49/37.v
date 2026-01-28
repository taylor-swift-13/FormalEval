Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_3_20 : modp_spec 3 20 8.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = Z.pow 2 n mod p *)
    (* 8 = 2^3 mod 20 *)
    (* 8 = 8 mod 20 *)
    (* 8 = 8 *)
    reflexivity.
Qed.