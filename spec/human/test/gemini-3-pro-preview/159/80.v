Require Import ZArith.
Require Import List.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

(* Definition of the precondition *)
Definition problem_159_pre (number need remaining : Z) : Prop :=
  0 <= number /\ 0 <= need /\ 0 <= remaining /\
  number <= 1000 /\ need <= 1000 /\ remaining <= 1000.

(* Definition of the specification *)
Definition problem_159_spec (number need remaining : Z) (result : list Z) : Prop :=
  (Z.ge remaining need /\ result = (number + need) :: (remaining - need) :: nil) \/
  (Z.lt remaining need /\ result = (number + remaining) :: 0 :: nil).

(* Proof for the specific test case: eat(6, 6, 6) -> [12, 0] *)
Example test_case_159: problem_159_pre 6 6 6 -> problem_159_spec 6 6 6 [12; 0].
Proof.
  (* Introduce the precondition hypothesis *)
  intros Hpre.
  
  (* Unfold the specification to expose the logic *)
  unfold problem_159_spec.
  
  (* Since remaining (6) >= need (6), we must prove the left side of the disjunction *)
  left.
  
  (* Split the conjunction into the condition check and the result calculation *)
  split.
  - (* Subgoal 1: Prove 6 >= 6 *)
    lia.
  - (* Subgoal 2: Prove [12; 0] matches the calculation [6 + 6; 6 - 6] *)
    (* Simplify the arithmetic expressions in the list *)
    simpl.
    (* Prove equality *)
    reflexivity.
Qed.