Require Import ZArith.
Require Import Lia.

Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_10_17 : modp_spec 10 17 4.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = Z.pow 2 n mod p *)
    (* 4 = 2^10 mod 17 *)
    (* 4 = 1024 mod 17 *)
    (* 4 = 4 *)
    reflexivity.
Qed.