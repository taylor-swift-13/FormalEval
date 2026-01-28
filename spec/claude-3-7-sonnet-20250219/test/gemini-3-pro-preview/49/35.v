Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_7_78 : modp_spec 7 78 50.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = Z.pow 2 n mod p *)
    (* 50 = 2^7 mod 78 *)
    (* 50 = 128 mod 78 *)
    (* 50 = 50 *)
    reflexivity.
Qed.