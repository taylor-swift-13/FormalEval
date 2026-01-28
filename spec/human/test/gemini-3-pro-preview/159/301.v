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

(* Proof for the specific test case: eat(498, 504, 800) -> [1002, 296] *)
Example test_case_159: problem_159_pre 498 504 800 -> problem_159_spec 498 504 800 [1002; 296].
Proof.
  intros Hpre.
  unfold problem_159_spec.
  left.
  split.
  - lia.
  - reflexivity.
Qed.