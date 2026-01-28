Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

(* 将 Z 的绝对值按十进制拆成数字序列 *)
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

(* 归纳计数：列表中偶数/奇数数字的个数 *)
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

(* 辅助引理：7的十进制展开为[7] *)
Lemma digits_of_7 : digits_of_Z 7 [7%nat].
Proof.
  apply doz_pos.
  - lia.
  - apply dop_step with (ds := []).
    + lia.
    + split.
      * apply Nat2Z.is_nonneg.
      * unfold Z.of_nat. simpl. lia.
    + unfold Z.of_nat. simpl. reflexivity.
    + apply dop_zero.
Qed.

(* 辅助引理：[7]的奇偶计数 *)
Lemma count_7 : count_even_odd_list [7%nat] 0 1.
Proof.
  apply ceo_cons_odd.
  - unfold Nat.even. simpl. reflexivity.
  - apply ceo_nil.
Qed.

Example test_case_7 : problem_155_spec 7 (0, 1).
Proof.
  unfold problem_155_spec.
  exists [7%nat].
  split.
  - apply digits_of_7.
  - apply count_7.
Qed.