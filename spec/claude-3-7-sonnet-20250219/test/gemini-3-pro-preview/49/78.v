Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_8_100 : modp_spec 8 100 56.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = Z.pow 2 n mod p *)
    (* 56 = 2^8 mod 100 *)
    (* 56 = 256 mod 100 *)
    (* 56 = 56 *)
    reflexivity.
Qed.