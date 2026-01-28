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

(* Test case proof *)
Example test_case_155 : problem_155_spec (-1111109) (1%nat, 6%nat).
Proof.
  unfold problem_155_spec.
  exists [9; 0; 1; 1; 1; 1; 1]%nat.
  split.
  - apply doz_neg.
    + lia.
    + simpl.
      apply dop_step with (n := 1111109) (d := 9%nat) (ds := [0; 1; 1; 1; 1; 1]%nat).
      * lia.
      * simpl; lia.
      * reflexivity.
      * replace (1111109 / 10) with 111110 by reflexivity.
        apply dop_step with (n := 111110) (d := 0%nat) (ds := [1; 1; 1; 1; 1]%nat).
        -- lia.
        -- simpl; lia.
        -- reflexivity.
        -- replace (111110 / 10) with 11111 by reflexivity.
           apply dop_step with (n := 11111) (d := 1%nat) (ds := [1; 1; 1; 1]%nat).
           ++ lia.
           ++ simpl; lia.
           ++ reflexivity.
           ++ replace (11111 / 10) with 1111 by reflexivity.
              apply dop_step with (n := 1111) (d := 1%nat) (ds := [1; 1; 1]%nat).
              ** lia.
              ** simpl; lia.
              ** reflexivity.
              ** replace (1111 / 10) with 111 by reflexivity.
                 apply dop_step with (n := 111) (d := 1%nat) (ds := [1; 1]%nat).
                 *** lia.
                 *** simpl; lia.
                 *** reflexivity.
                 *** replace (111 / 10) with 11 by reflexivity.
                     apply dop_step with (n := 11) (d := 1%nat) (ds := [1]%nat).
                     ---- lia.
                     ---- simpl; lia.
                     ---- reflexivity.
                     ---- replace (11 / 10) with 1 by reflexivity.
                          apply dop_step with (n := 1) (d := 1%nat) (ds := []).
                          ++++ lia.
                          ++++ simpl; lia.
                          ++++ reflexivity.
                          ++++ replace (1 / 10) with 0 by reflexivity.
                               apply dop_zero.
  - apply ceo_cons_odd. { reflexivity. }
    apply ceo_cons_even. { reflexivity. }
    apply ceo_cons_odd. { reflexivity. }
    apply ceo_cons_odd. { reflexivity. }
    apply ceo_cons_odd. { reflexivity. }
    apply ceo_cons_odd. { reflexivity. }
    apply ceo_cons_odd. { reflexivity. }
    apply ceo_nil.
Qed.