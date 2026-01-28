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

(* Proof for the specific test case: eat(599, 500, 600) -> [1099, 100] *)
Example test_case_159: problem_159_pre 599 500 600 -> problem_159_spec 599 500 600 [1099; 100].
Proof.
  (* Introduce the precondition hypothesis *)
  intros Hpre.
  
  (* Unfold the specification to expose the logic *)
  unfold problem_159_spec.
  
  (* Since remaining (600) >= need (500), we must prove the left side of the disjunction *)
  left.
  
  (* Split the conjunction into the condition check and the result calculation *)
  split.
  - (* Subgoal 1: Prove 600 >= 500 *)
    lia.
  - (* Subgoal 2: Prove [1099; 100] matches the calculation [599 + 500; 600 - 500] *)
    (* Simplify the arithmetic expressions in the list *)
    simpl.
    (* Prove equality *)
    reflexivity.
Qed.