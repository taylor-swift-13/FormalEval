Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition rolling_max_spec (numbers result : list Z) : Prop :=
  length result = length numbers /\
  forall i,
    (i < length numbers)%nat ->
    nth i result 0 = 
      match firstn (i + 1) numbers with
      | [] => 0
      | x :: xs => fold_left Z.max xs x
      end.

Example test_rolling_max_1 : 
  rolling_max_spec [5; 4; -3; 2; 1; 5] [5; 5; 5; 5; 5; 5].
Proof.
  unfold rolling_max_spec.
  split.
  - (* length condition *)
    simpl. reflexivity.
  - (* element-wise condition *)
    intros i H.
    destruct i; [simpl; reflexivity |].
    destruct i; [simpl; reflexivity |].
    destruct i; [simpl; reflexivity |].
    destruct i; [simpl; reflexivity |].
    destruct i; [simpl; reflexivity |].
    destruct i; [simpl; reflexivity |].
    simpl in H. lia.
Qed.