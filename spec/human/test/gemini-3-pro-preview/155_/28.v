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
Example test_case_155 : problem_155_spec 2369 (2%nat, 2%nat).
Proof.
  unfold problem_155_spec.
  (* The digits of 2369 are [9; 6; 3; 2] in reverse order of generation (LSD first) *)
  exists [9; 6; 3; 2]%nat.
  split.
  - (* Prove digits_of_Z 2369 [9; 6; 3; 2] *)
    apply doz_pos.
    + lia. (* 0 < 2369 *)
    + apply dop_step with (n := 2369) (d := 9%nat) (ds := [6; 3; 2]%nat).
      * lia.
      * simpl; lia.
      * reflexivity.
      * replace (2369 / 10) with 236 by reflexivity.
        apply dop_step with (n := 236) (d := 6%nat) (ds := [3; 2]%nat).
        { lia. }
        { simpl; lia. }
        { reflexivity. }
        { replace (236 / 10) with 23 by reflexivity.
          apply dop_step with (n := 23) (d := 3%nat) (ds := [2]%nat).
          { lia. }
          { simpl; lia. }
          { reflexivity. }
          { replace (23 / 10) with 2 by reflexivity.
            apply dop_step with (n := 2) (d := 2%nat) (ds := []).
            { lia. }
            { simpl; lia. }
            { reflexivity. }
            { replace (2 / 10) with 0 by reflexivity. apply dop_zero. }
          }
        }
  - (* Prove count_even_odd_list [9; 6; 3; 2] 2 2 *)
    apply ceo_cons_odd.
    + reflexivity. (* 9 is odd *)
    + apply ceo_cons_even.
      * reflexivity. (* 6 is even *)
      * apply ceo_cons_odd.
        { reflexivity. } (* 3 is odd *)
        { apply ceo_cons_even.
          { reflexivity. } (* 2 is even *)
          { apply ceo_nil. }
        }
Qed.