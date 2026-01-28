Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* Definition provided in the prompt *)
Inductive digits_of_posZ : Z -> list nat -> Prop :=
| dop_zero : digits_of_posZ 0%Z []
| dop_step : forall n (d : nat) ds,
   0 < n -> (0 <= Z.of_nat d < 10%Z) ->
   Z.of_nat d = n mod 10 ->
   digits_of_posZ (n / 10) ds ->
   digits_of_posZ n (d :: ds).

Definition absZ (n : Z) : Z := Z.abs n.

Inductive digits_of_Z : Z -> list nat -> Prop :=
| doz_zero_empty : digits_of_Z 0%Z []
| doz_pos : forall n ds, 0 < n -> digits_of_posZ n ds -> digits_of_Z n ds
| doz_neg : forall n ds, n < 0 -> digits_of_posZ (absZ n) ds -> digits_of_Z n ds.

Inductive count_even_odd_list : list nat -> nat -> nat -> Prop :=
| ceo_nil : count_even_odd_list [] 0%nat 0%nat
| ceo_cons_even : forall d t e o,
    Nat.even d = true ->
    count_even_odd_list t e o ->
    count_even_odd_list (d :: t) (S e) o
| ceo_cons_odd : forall d t e o,
    Nat.even d = false ->
    count_even_odd_list t e o ->
    count_even_odd_list (d :: t) e (S o).

Definition problem_155_pre (num : Z) : Prop := True.

Definition problem_155_spec (num : Z) (output : nat * nat) : Prop :=
  let '(e, o) := output in
  exists ds : list nat, digits_of_Z num ds /\ count_even_odd_list ds e o.

Example test_case_155 : problem_155_spec (-123456790) (4%nat, 5%nat).
Proof.
  unfold problem_155_spec.
  exists [0; 9; 7; 6; 5; 4; 3; 2; 1]%nat.
  split.
  - apply doz_neg.
    + lia.
    + unfold absZ. simpl.
      apply dop_step with (n := 123456790) (d := 0%nat) (ds := [9; 7; 6; 5; 4; 3; 2; 1]%nat); [lia | lia | reflexivity |].
      apply dop_step with (n := 12345679) (d := 9%nat) (ds := [7; 6; 5; 4; 3; 2; 1]%nat); [lia | lia | reflexivity |].
      apply dop_step with (n := 1234567) (d := 7%nat) (ds := [6; 5; 4; 3; 2; 1]%nat); [lia | lia | reflexivity |].
      apply dop_step with (n := 123456) (d := 6%nat) (ds := [5; 4; 3; 2; 1]%nat); [lia | lia | reflexivity |].
      apply dop_step with (n := 12345) (d := 5%nat) (ds := [4; 3; 2; 1]%nat); [lia | lia | reflexivity |].
      apply dop_step with (n := 1234) (d := 4%nat) (ds := [3; 2; 1]%nat); [lia | lia | reflexivity |].
      apply dop_step with (n := 123) (d := 3%nat) (ds := [2; 1]%nat); [lia | lia | reflexivity |].
      apply dop_step with (n := 12) (d := 2%nat) (ds := [1]%nat); [lia | lia | reflexivity |].
      apply dop_step with (n := 1) (d := 1%nat) (ds := []%nat); [lia | lia | reflexivity |].
      apply dop_zero.
  - repeat (first [ apply ceo_cons_even; [ reflexivity | ] | apply ceo_cons_odd; [ reflexivity | ] ]).
    apply ceo_nil.
Qed.