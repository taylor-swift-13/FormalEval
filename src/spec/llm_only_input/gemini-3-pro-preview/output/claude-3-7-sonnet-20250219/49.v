Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition modp_spec (n p res : Z) : Prop :=
  p > 0 /\
  res = Z.pow 2 n mod p.

Example test_modp_spec : modp_spec 3 5 3.
Proof.
  unfold modp_spec.
  split.
  - (* Prove p > 0 *)
    lia.
  - (* Prove res = 2^n mod p *)
    (* Z.pow 2 3 simplifies to 8 *)
    (* 8 mod 5 simplifies to 3 *)
    simpl.
    reflexivity.
Qed.