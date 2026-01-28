Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_7_6 : modp_spec 7 6 2.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = Z.pow 2 n mod p *)
    (* 2 = 2^7 mod 6 *)
    (* 2 = 128 mod 6 *)
    (* 2 = 2 *)
    reflexivity.
Qed.