Require Import ZArith.
Require Import List.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

Definition problem_159_pre (number need remaining : Z) : Prop :=
  0 <= number /\ 0 <= need /\ 0 <= remaining /\
  number <= 1000 /\ need <= 1000 /\ remaining <= 1000.

Definition problem_159_spec (number need remaining : Z) (result : list Z) : Prop :=
  (Z.ge remaining need /\ result = (number + need) :: (remaining - need) :: nil) \/
  (Z.lt remaining need /\ result = (number + remaining) :: 0 :: nil).

Example test_case_159: problem_159_pre 500 800 700 -> problem_159_spec 500 800 700 [1200; 0].
Proof.
  intros Hpre.
  unfold problem_159_spec.
  right.
  split.
  - lia.
  - simpl. reflexivity.
Qed.