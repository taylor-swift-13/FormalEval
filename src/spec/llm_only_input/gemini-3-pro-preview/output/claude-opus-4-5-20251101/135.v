Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.

Import ListNotations.

Open Scope Z_scope.

Definition nth_Z (l : list Z) (n : nat) (default : Z) : Z :=
  nth n l default.

Definition is_valid_index (arr : list Z) (i : nat) : Prop :=
  (i > 0)%nat /\ (i < length arr)%nat /\
  nth_Z arr i 0 < nth_Z arr (i - 1) 0.

Definition no_larger_valid_index (arr : list Z) (i : nat) : Prop :=
  forall j : nat, (j > i)%nat -> (j < length arr)%nat ->
    nth_Z arr j 0 >= nth_Z arr (j - 1) 0.

Definition no_valid_index (arr : list Z) : Prop :=
  forall i : nat, (i > 0)%nat -> (i < length arr)%nat ->
    nth_Z arr i 0 >= nth_Z arr (i - 1) 0.

Definition can_arrange_spec (arr : list Z) (result : Z) : Prop :=
  (exists i : nat,
    is_valid_index arr i /\
    no_larger_valid_index arr i /\
    result = Z.of_nat i) \/
  (no_valid_index arr /\ result = -1).

Example test_case : can_arrange_spec [1; 2; 4; 3; 5] 3.
Proof.
  unfold can_arrange_spec.
  (* The index 3 satisfies the condition, so we choose the left branch *)
  left.
  exists 3%nat.
  split.
  - (* Verify is_valid_index for i = 3 *)
    unfold is_valid_index.
    simpl.
    split; [lia | split; [lia | lia]].
  - split.
    + (* Verify no_larger_valid_index for i = 3 *)
      unfold no_larger_valid_index.
      intros j Hgt Hlt.
      (* Simplify Hlt to reveal the length of the list, allowing lia to work *)
      simpl in Hlt. 
      (* The only natural number j such that 3 < j < 5 is 4 *)
      assert (j = 4%nat) by lia.
      subst j.
      (* Verify the condition for j = 4: arr[4] >= arr[3] => 5 >= 3 *)
      simpl.
      lia.
    + (* Verify result matches *)
      simpl.
      reflexivity.
Qed.