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

Example test_can_arrange : can_arrange_spec [1; 2; 4; 3; 5] 3.
Proof.
  unfold can_arrange_spec.
  left.
  exists 3%nat.
  split.
  { (* Prove is_valid_index *)
    unfold is_valid_index.
    split.
    - lia.
    - split.
      + simpl. lia.
      + unfold nth_Z. simpl. lia.
  }
  split.
  { (* Prove no_larger_valid_index *)
    unfold no_larger_valid_index.
    intros j Hgt Hlen.
    (* Since j > 3 and j < 5, j must be 4 *)
    assert (j = 4%nat) as Hj by lia.
    subst j.
    unfold nth_Z. simpl. lia.
  }
  { (* Prove result equality *)
    simpl. reflexivity.
  }
Qed.