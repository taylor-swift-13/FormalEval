Require Import Arith.
Require Import ZArith.
Require Import ZArith.Zpow_facts.
Open Scope Z_scope.

Definition problem_76_pre (x n : Z) : Prop := True.

Definition problem_76_spec (x n : Z) (result : bool) : Prop :=
  result = true <-> (exists k : nat, x = n ^ (Z.of_nat k)).

Example test_case : problem_76_spec 5 5 true.
Proof.
  (* Unfold the specification definition *)
  unfold problem_76_spec.
  
  (* The goal is an equivalence: true = true <-> exists k, 5 = 5^k *)
  split.
  
  - (* Left to Right: true = true -> exists k, 5 = 5^k *)
    intros _.
    (* We need to provide a natural number k such that 5^k = 5. k = 1 works. *)
    exists 1%nat.
    (* Simplify the expression 5 ^ (Z.of_nat 1) *)
    simpl.
    (* Verify that 5 = 5 *)
    reflexivity.
    
  - (* Right to Left: (exists k, 5 = 5^k) -> true = true *)
    intros _.
    (* true = true is trivially true *)
    reflexivity.
Qed.