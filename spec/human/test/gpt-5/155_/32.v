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

Example even_odd_count_test_neg_589 :
  problem_155_spec (-589%Z) (1%nat, 2%nat).
Proof.
  unfold problem_155_spec.
  simpl.
  exists [9%nat; 8%nat; 5%nat].
  split.
  - apply doz_neg.
    + lia.
    + replace (absZ (-589%Z)) with 589%Z by (vm_compute; reflexivity).
      apply (dop_step 589%Z 9%nat [8%nat; 5%nat]).
      * lia.
      * split; lia.
      * replace (Z.of_nat 9%nat) with 9%Z by reflexivity.
        assert (Hmod1 : 589%Z mod 10%Z = 9%Z) by (vm_compute; reflexivity).
        rewrite Hmod1. reflexivity.
      * assert (Hdiv1 : 589%Z / 10%Z = 58%Z) by (vm_compute; reflexivity).
        rewrite Hdiv1.
        apply (dop_step 58%Z 8%nat [5%nat]).
        -- lia.
        -- split; lia.
        -- replace (Z.of_nat 8%nat) with 8%Z by reflexivity.
           assert (Hmod2 : 58%Z mod 10%Z = 8%Z) by (vm_compute; reflexivity).
           rewrite Hmod2. reflexivity.
        -- assert (Hdiv2 : 58%Z / 10%Z = 5%Z) by (vm_compute; reflexivity).
           rewrite Hdiv2.
           apply (dop_step 5%Z 5%nat []).
           ++ lia.
           ++ split; lia.
           ++ replace (Z.of_nat 5%nat) with 5%Z by reflexivity.
              assert (Hmod3 : 5%Z mod 10%Z = 5%Z) by (vm_compute; reflexivity).
              rewrite Hmod3. reflexivity.
           ++ assert (Hdiv3 : 5%Z / 10%Z = 0%Z) by (vm_compute; reflexivity).
              rewrite Hdiv3.
              apply dop_zero.
  - apply ceo_cons_odd.
    + simpl. reflexivity.
    + apply ceo_cons_even.
      * simpl. reflexivity.
      * apply ceo_cons_odd.
        -- simpl. reflexivity.
        -- apply ceo_nil.
Qed.