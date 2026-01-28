Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_6_78 : modp_spec 6 78 64.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = Z.pow 2 n mod p *)
    (* 64 = 2^6 mod 78 *)
    (* 64 = 64 mod 78 *)
    (* 64 = 64 *)
    reflexivity.
Qed.