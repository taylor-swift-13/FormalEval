Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_0_101 : modp_spec 0 101 1.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = Z.pow 2 n mod p *)
    (* 1 = 2^0 mod 101 *)
    (* 1 = 1 mod 101 *)
    (* 1 = 1 *)
    reflexivity.
Qed.