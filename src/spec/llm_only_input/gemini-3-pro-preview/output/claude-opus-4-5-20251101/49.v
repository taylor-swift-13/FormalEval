Require Import ZArith.
Require Import Zdiv.
Require Import Psatz. (* Required for lia tactic *)

Open Scope Z_scope.

Definition modp_spec (n : Z) (p : Z) (result : Z) : Prop :=
  p > 0 /\ result = (2 ^ n) mod p.

Example test_modp : modp_spec 3 5 3.
Proof.
  (* Unfold the specification definition *)
  unfold modp_spec.
  
  (* Split the conjunction into two subgoals *)
  split.
  
  - (* Subgoal 1: Prove 5 > 0 *)
    lia.
    
  - (* Subgoal 2: Prove 3 = (2 ^ 3) mod 5 *)
    (* 2 ^ 3 = 8 *)
    (* 8 mod 5 = 3 *)
    (* vm_compute performs the arithmetic calculation efficiently *)
    vm_compute.
    reflexivity.
Qed.