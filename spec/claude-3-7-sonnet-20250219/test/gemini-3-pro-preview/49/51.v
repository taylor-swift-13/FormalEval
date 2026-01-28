Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_17_17 : modp_spec 17 17 2.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = Z.pow 2 n mod p *)
    (* 2 = 2^17 mod 17 *)
    (* 2 = 131072 mod 17 *)
    (* 2 = 2 *)
    reflexivity.
Qed.