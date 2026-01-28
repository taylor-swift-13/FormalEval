Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint prefix_max (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: xs =>
    match prefix_max xs with
    | [] => [x]
    | y :: ys =>
      let m := Z.max x y in
      m :: ys
    end
  end.

Definition rolling_max_spec (numbers result : list Z) : Prop :=
  length result = length numbers /\
  forall i,
    (i < length numbers)%nat ->
    nth i result 0 = 
      match firstn (i + 1)%nat numbers with
      | [] => 0
      | x :: xs => fold_left Z.max xs x
      end.

Example test_rolling_max_1 : rolling_max_spec [4; -3; -4; -4; -3; -2; -1; -2; -3; 4; 8] [4; 4; 4; 4; 4; 4; 4; 4; 4; 4; 8].
Proof.
  unfold rolling_max_spec.
  split.
  - (* length condition *)
    simpl. reflexivity.
  - (* element-wise condition *)
    intros i H.
    repeat (destruct i; [ simpl; reflexivity | ]).
    simpl in H. lia.
Qed.