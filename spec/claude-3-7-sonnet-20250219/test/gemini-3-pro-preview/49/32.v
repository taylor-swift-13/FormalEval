Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_5_5 : modp_spec 5 5 2.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = Z.pow 2 n mod p *)
    (* 2 = 2^5 mod 5 *)
    (* 2 = 32 mod 5 *)
    (* 2 = 2 *)
    reflexivity.
Qed.