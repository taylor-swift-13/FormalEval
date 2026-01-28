Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_6_21 : modp_spec 6 21 1.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = Z.pow 2 n mod p *)
    (* 1 = 2^6 mod 21 *)
    (* 1 = 64 mod 21 *)
    (* 1 = 1 *)
    reflexivity.
Qed.