Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Bool.Bool Coq.Init.Nat.
Import ListNotations.
Open Scope Z_scope.

Inductive to_digits_Z_rel : Z -> list nat -> Prop :=
| tdz_zero : to_digits_Z_rel 0%Z nil
| tdz_step : forall n d ds, 0 < n -> d = Z.to_nat (n mod 10) ->
   to_digits_Z_rel (n / 10) ds ->
   to_digits_Z_rel n (d :: ds).

Inductive digits_of_Z_rel : Z -> list nat -> Prop :=
| doz_zero : digits_of_Z_rel 0%Z nil
| doz_pos : forall n ds, 0 < n -> to_digits_Z_rel n ds -> digits_of_Z_rel n ds.

Inductive sum_digits_rel_from_list : list nat -> Z -> Prop :=
| sdrfl_nil : sum_digits_rel_from_list nil 0%Z
| sdrfl_cons : forall d ds s, sum_digits_rel_from_list ds s ->
   sum_digits_rel_from_list (d :: ds) (Z.of_nat d + s).

(* most-significant digit: since digits lists are produced with least-significant
   digit at head, the msd is the last element of the list *)
Inductive msd_of_digits : list nat -> nat -> Prop :=
| mod_single : forall d, msd_of_digits (d :: nil) d
| mod_cons : forall d ds m, msd_of_digits ds m -> msd_of_digits (d :: ds) m.

Inductive sum_digits_rel : Z -> Z -> Prop :=
| sdr_zero : sum_digits_rel 0%Z 0%Z
| sdr_pos : forall n s ds, 0 < n -> digits_of_Z_rel n ds -> sum_digits_rel_from_list ds s ->
   sum_digits_rel n s
| sdr_neg : forall n s p ds s_pos m,
    n < 0 ->
    p = Z.to_nat (- n) ->
    digits_of_Z_rel (Z.of_nat p) ds ->
    sum_digits_rel_from_list ds s_pos ->
    msd_of_digits ds m ->
    s = s_pos - 2 * (Z.of_nat m) ->
    sum_digits_rel n s.

Inductive count_nums_rel : list Z -> nat -> Prop :=
| cnr_nil : count_nums_rel nil 0%nat
| cnr_hit : forall h t n s, sum_digits_rel h s -> s > 0%Z -> count_nums_rel t n ->
   count_nums_rel (h :: t) (S n)
| cnr_miss : forall h t n s, sum_digits_rel h s -> (s <= 0%Z) -> count_nums_rel t n ->
   count_nums_rel (h :: t) n.

(* 输入列表可为任意整数列表 *)
Definition problem_108_pre (l : list Z) : Prop := True.

Definition problem_108_spec (l : list Z) (output : nat) : Prop :=
  count_nums_rel l output.

Example test_case : problem_108_spec [1%Z] 1%nat.
Proof.
  unfold problem_108_spec.
  apply cnr_hit with (s := 1%Z).
  - apply sdr_pos with (ds := [1%nat]).
    + reflexivity.
    + apply doz_pos.
      * reflexivity.
      * apply tdz_step with (n := 1%Z) (d := 1%nat) (ds := []).
        -- reflexivity.
        -- reflexivity.
        -- apply tdz_zero.
    + change 1%Z with (Z.of_nat 1 + 0)%Z.
      apply sdrfl_cons.
      apply sdrfl_nil.
  - reflexivity.
  - apply cnr_nil.
Qed.