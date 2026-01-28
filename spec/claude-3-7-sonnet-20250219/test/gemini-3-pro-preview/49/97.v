Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_7_20 : modp_spec 7 20 8.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = Z.pow 2 n mod p *)
    (* 8 = 2^7 mod 20 *)
    (* 8 = 128 mod 20 *)
    (* 8 = 8 *)
    reflexivity.
Qed.