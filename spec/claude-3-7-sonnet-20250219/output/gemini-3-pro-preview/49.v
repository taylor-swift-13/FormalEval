Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_3_5 : modp_spec 3 5 3.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = Z.pow 2 n mod p *)
    (* 3 = 2^3 mod 5 *)
    (* 3 = 8 mod 5 *)
    (* 3 = 3 *)
    reflexivity.
Qed.