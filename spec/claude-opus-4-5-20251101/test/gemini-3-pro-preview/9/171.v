Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

Fixpoint max_list (l : list Z) (default : Z) : Z :=
  match l with
  | [] => default
  | x :: xs => Z.max x (max_list xs x)
  end.

Fixpoint firstn {A : Type} (n : nat) (l : list A) : list A :=
  match n with
  | O => []
  | S n' => match l with
            | [] => []
            | x :: xs => x :: firstn n' xs
            end
  end.

Fixpoint rolling_max_aux (numbers : list Z) (idx : nat) : list Z :=
  match idx with
  | O => []
  | S n => rolling_max_aux numbers n ++ [max_list (firstn idx numbers) 0]
  end.

Definition rolling_max (numbers : list Z) : list Z :=
  rolling_max_aux numbers (length numbers).

Definition rolling_max_spec (numbers : list Z) (result : list Z) : Prop :=
  length result = length numbers /\
  forall i : nat, (i < length numbers)%nat ->
    nth i result 0 = max_list (firstn (S i) numbers) 0.

Example test_rolling_max_case1 : rolling_max_spec 
  [-1%Z; -2%Z; -3%Z; -2%Z; -3%Z; -4%Z; -3%Z; -2%Z; -1%Z; -2%Z; -3%Z; -4%Z; -5%Z; -3%Z; -2%Z; -1%Z; 0%Z; -1%Z; -2%Z; -2%Z; -2%Z; -1%Z; 0%Z; -3%Z; 1%Z; 0%Z; -1%Z; -2%Z; -4%Z]
  [-1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; -1%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z].
Proof.
  unfold rolling_max_spec.
  split.
  - simpl. reflexivity.
  - intros i H.
    do 29 (destruct i; [ vm_compute; reflexivity | ]).
    exfalso; simpl in H; lia.
Qed.