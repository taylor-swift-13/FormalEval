Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

Open Scope Z_scope.

Definition is_prime (p : Z) : Prop :=
  p >= 2 /\
  forall d : Z, 2 <= d -> d < p -> ~(p mod d = 0).

Definition count_up_to_spec (n : Z) (result : list Z) : Prop :=
  n >= 0 /\
  (forall x, In x result <-> (is_prime x /\ 2 <= x < n)) /\
  (forall i j, 0 <= i < j -> j < Z.of_nat (length result) ->
    nth (Z.to_nat i) result 0 < nth (Z.to_nat j) result 0).

Example test_count_up_to_2: count_up_to_spec 2 [].
Proof.
  unfold count_up_to_spec.
  split.
  - (* n >= 0 *)
    lia.
  - split.
    + (* Membership property *)
      intros x.
      split.
      * (* Forward: In x [] -> ... *)
        intros H_in.
        inversion H_in.
      * (* Backward: is_prime x /\ 2 <= x < 2 -> In x [] *)
        intros [H_prime H_range].
        lia.
    + (* Sorted property *)
      intros i j H_lt H_bound.
      simpl in H_bound.
      (* length [] is 0, so j < 0, which contradicts 0 <= i < j *)
      lia.
Qed.