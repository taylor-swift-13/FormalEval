Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

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

Example even_odd_count_test_neg_78 :
  problem_155_spec (-78%Z) (1%nat, 1%nat).
Proof.
  unfold problem_155_spec.
  simpl.
  exists [8%nat; 7%nat].
  split.
  - apply doz_neg.
    + lia.
    + apply (dop_step (absZ (-78%Z)) 8%nat [7%nat]).
      * simpl. lia.
      * split; lia.
      * replace (Z.of_nat 8%nat) with 8%Z by reflexivity.
        vm_compute. reflexivity.
      * assert (Hdiv : (absZ (-78%Z)) / 10%Z = 7%Z) by (vm_compute; reflexivity).
        rewrite Hdiv.
        apply (dop_step 7%Z 7%nat []).
        -- lia.
        -- split; lia.
        -- replace (Z.of_nat 7%nat) with 7%Z by reflexivity.
           symmetry.
           apply Z.mod_small; split; lia.
        -- assert (Hdiv7 : 7%Z / 10%Z = 0%Z) by (apply Z.div_small; split; lia).
           rewrite Hdiv7.
           apply dop_zero.
  - apply ceo_cons_even.
    + simpl. reflexivity.
    + apply ceo_cons_odd.
      * simpl. reflexivity.
      * apply ceo_nil.
Qed.