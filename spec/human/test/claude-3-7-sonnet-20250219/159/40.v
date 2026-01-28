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
  problem_159_pre 10 5 10 /\
  problem_159_spec 10 5 10 [15;5].
Proof.
  split.
  - (* precondition *)
    unfold problem_159_pre.
    repeat split; lia.
  - (* specification *)
    unfold problem_159_spec.
    left.
    split.
    + lia.
    + reflexivity.
Qed.