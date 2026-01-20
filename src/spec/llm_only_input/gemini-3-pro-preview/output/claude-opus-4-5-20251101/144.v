Require Import ZArith.
Require Import Bool.
Require Import Psatz.

Open Scope Z_scope.

Definition simplify_spec (x1 x2 n1 n2 : Z) (result : bool) : Prop :=
  x2 > 0 /\ n2 > 0 /\
  ((x1 * n1) mod (x2 * n2) = 0 <-> result = true).

(* 
   Test case mapping:
   Input: ["1/5"; "5/1"] -> x1=1, x2=5, n1=5, n2=1
   Output: true
*)
Example test_case_simplify: simplify_spec 1 5 5 1 true.
Proof.
  (* Unfold the specification definition *)
  unfold simplify_spec.
  
  (* Split the conjunction x2 > 0 /\ ... *)
  split.
  - (* Subgoal 1: 5 > 0 *)
    lia.
    
  - (* Handle the remaining conjunction n2 > 0 /\ ... *)
    split.
    + (* Subgoal 2: 1 > 0 *)
      lia.
      
    + (* Handle the equivalence *)
      split.
      * (* Subgoal 3: (1 * 5) mod (5 * 1) = 0 -> true = true *)
        intros H.
        reflexivity.
        
      * (* Subgoal 4: true = true -> (1 * 5) mod (5 * 1) = 0 *)
        intros H.
        (* Simplify the arithmetic expression: 1*5=5, 5*1=5, 5 mod 5 = 0 *)
        compute.
        reflexivity.
Qed.