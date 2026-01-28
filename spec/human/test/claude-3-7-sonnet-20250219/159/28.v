Require Import ZArith.
Require Import Lia.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Definition problem_159_pre (number need remaining : Z) : Prop :=
  0 <= number /\ 0 <= need /\ 0 <= remaining /\
  number <= 1000 /\ need <= 1000 /\ remaining <= 1000.

Definition problem_159_spec (number need remaining : Z) (result : list Z) : Prop :=
  (Z.ge remaining need /\ result = (number + need) :: (remaining - need) :: nil) \/
  (Z.lt remaining need /\ result = (number + remaining) :: 0 :: nil).

Example problem_159_example :
  problem_159_pre 0 4 0 /\
  problem_159_spec 0 4 0 [0;0].
Proof.
  split.
  - unfold problem_159_pre.
    repeat split; lia.
  - unfold problem_159_spec.
    right.
    split.
    + lia.
    + reflexivity.
Qed.