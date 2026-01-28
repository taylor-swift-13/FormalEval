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

Example test_problem_159_pre : problem_159_pre 999%Z 701%Z 700%Z.
Proof.
  unfold problem_159_pre.
  repeat split; lia.
Qed.

Example test_problem_159_spec : problem_159_spec 999%Z 701%Z 700%Z [1699%Z; 0%Z].
Proof.
  unfold problem_159_spec.
  right.
  split.
  - lia.
  - now compute.
Qed.