Require Import ZArith.
Require Import List.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition problem_159_pre (number need remaining : Z) : Prop :=
  0 <= number /\ 0 <= need /\ 0 <= remaining /\
  number <= 1000 /\ need <= 1000 /\ remaining <= 1000.

Definition problem_159_spec (number need remaining : Z) (result : list Z) : Prop :=
  (Z.ge remaining need /\ result = (number + need) :: (remaining - need) :: nil) \/
  (Z.lt remaining need /\ result = (number + remaining) :: 0 :: nil).

Example test_eat_2 : problem_159_spec 9 999 4 [13; 0].
Proof.
  unfold problem_159_spec.
  right.
  split.
  - lia.
  - simpl.
    reflexivity.
Qed.