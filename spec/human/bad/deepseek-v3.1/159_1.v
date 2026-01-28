Require Import ZArith.
Require Import List.
Import ListNotations.
Open Scope Z_scope.

Definition problem_159_pre (number need remaining : Z) : Prop :=
  0 <= number /\ 0 <= need /\ 0 <= remaining /\
  number <= 1000 /\ need <= 1000 /\ remaining <= 1000.

Definition problem_159_spec (number need remaining : Z) (result : list Z) : Prop :=
  (Z.ge remaining need /\ result = (number + need) :: (remaining - need) :: nil) \/
  (Z.lt remaining need /\ result = (number + remaining) :: 0 :: nil).

Example test_eat_example1 :
  problem_159_pre 5 6 10 /\
  problem_159_spec 5 6 10 [11; 4].
Proof.
  split.
  - unfold problem_159_pre.
    repeat split; try (apply Z.le_refl); try (apply Zle_0_1000).
  - unfold problem_159_spec.
    left.
    split.
    + unfold Z.ge.
      apply Z.le_ge.
      apply Z.le_refl.
    + simpl.
      reflexivity.
Qed.