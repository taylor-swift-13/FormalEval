Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
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
    nth i result 0 = fold_left Z.max (firstn (i + 1)%nat numbers) 0.

Example test_rolling_max_1 : rolling_max_spec 
  [0%Z; 4%Z; -3%Z; -4%Z; -5%Z; -4%Z; -3%Z; -2%Z; -1%Z; -2%Z; -3%Z] 
  [0%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z; 4%Z].
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