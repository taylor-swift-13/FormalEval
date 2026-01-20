Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition pluck_spec (arr : list Z) (res : list Z) : Prop :=
  ( (* Case 1: No even numbers exist in the array *)
    (forall x, In x arr -> Z.odd x = true) /\ res = []
  ) \/
  ( (* Case 2: Even numbers exist *)
    exists (v : Z) (i : Z),
      res = [v; i] /\
      (* The index i is within valid bounds *)
      0 <= i < Z.of_nat (length arr) /\
      (* The value v is located at index i *)
      nth_error arr (Z.to_nat i) = Some v /\
      (* The value is even *)
      Z.even v = true /\
      (* v is the smallest even value in the list *)
      (forall x, In x arr -> Z.even x = true -> v <= x) /\
      (* i is the smallest index among those containing the value v *)
      (* Since v is the minimum even, this implies no even number at j < i can be <= v *)
      (forall j x, 0 <= j < i -> nth_error arr (Z.to_nat j) = Some x -> Z.even x = true -> v < x)
  ).

Example pluck_test1 : pluck_spec [4%Z; 2%Z; 3%Z] [2%Z; 1%Z].
Proof.
  unfold pluck_spec.
  right.
  exists 2%Z, 1%Z.
  split.
  - (* res = [2; 1] *)
    reflexivity.
  - split.
    + (* 0 <= 1 < 3 *)
      simpl. lia.
    + split.
      * (* nth_error [4; 2; 3] 1 = Some 2 *)
        simpl. reflexivity.
      * split.
        -- (* Z.even 2 = true *)
           simpl. reflexivity.
        -- split.
           ++ (* 2 is the smallest even value *)
              intros x Hin Heven.
              simpl in Hin.
              destruct Hin as [H | [H | [H | H]]].
              ** subst x. lia.
              ** subst x. lia.
              ** subst x. simpl in Heven. discriminate.
              ** contradiction.
           ++ (* i=1 is the smallest index with value 2 *)
              intros j x Hj Hnth Heven.
              assert (Hj0: j = 0) by lia.
              subst j.
              simpl in Hnth.
              injection Hnth as Hx.
              subst x.
              simpl in Heven.
              lia.
Qed.