Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

(* Specification definition *)
Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 1 -> result = (2 ^ n) mod p.

(* Test case: input = [3%Z; 5%Z], output = 3%Z *)
Example test_modp : modp_spec 3 5 3.
Proof.
  (* Unfold the definition of the specification *)
  unfold modp_spec.

  (* Introduce the hypothesis that p > 1 (here 5 > 1) *)
  intros H.

  (* The goal is to prove 3 = (2 ^ 3) mod 5.
     Coq computes 2^3 = 8, and 8 mod 5 = 3 automatically. *)
  reflexivity.
Qed.