Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_5_17 : modp_spec 5 17 15.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = Z.pow 2 n mod p *)
    (* 15 = 2^5 mod 17 *)
    (* 15 = 32 mod 17 *)
    (* 15 = 15 *)
    reflexivity.
Qed.