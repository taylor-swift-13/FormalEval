Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.PeanoNat.
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

Definition input := [10; 5; 20; 30; 25; 20; 15; 10; 19].
Definition expected_output := [10; 10; 20; 30; 30; 30; 30; 30; 30].

Example test_rolling_max : rolling_max input = expected_output.
Proof.
  native_cast_no_check (eq_refl expected_output).
Qed.

Example test_rolling_max_spec : rolling_max_spec input expected_output.
Proof.
  unfold rolling_max_spec, input, expected_output.
  split.
  - reflexivity.
  - intros i H.
    do 9 (destruct i; [reflexivity|]).
    simpl in H. lia.
Qed.