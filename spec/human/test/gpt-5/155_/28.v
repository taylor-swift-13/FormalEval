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

Example even_odd_count_test_2369 :
  problem_155_spec 2369%Z (2%nat, 2%nat).
Proof.
  unfold problem_155_spec.
  simpl.
  exists [9%nat; 6%nat; 3%nat; 2%nat].
  split.
  - apply doz_pos.
    + lia.
    + apply (dop_step 2369%Z 9%nat [6%nat; 3%nat; 2%nat]).
      * lia.
      * split; lia.
      * replace (Z.of_nat 9%nat) with 9%Z by reflexivity.
        assert (Hmod1 : 2369%Z mod 10%Z = 9%Z) by (vm_compute; reflexivity).
        rewrite Hmod1. reflexivity.
      * replace (2369%Z / 10%Z) with 236%Z by (vm_compute; reflexivity).
        apply (dop_step 236%Z 6%nat [3%nat; 2%nat]).
        -- lia.
        -- split; lia.
        -- replace (Z.of_nat 6%nat) with 6%Z by reflexivity.
           assert (Hmod2 : 236%Z mod 10%Z = 6%Z) by (vm_compute; reflexivity).
           rewrite Hmod2. reflexivity.
        -- replace (236%Z / 10%Z) with 23%Z by (vm_compute; reflexivity).
           apply (dop_step 23%Z 3%nat [2%nat]).
           ++ lia.
           ++ split; lia.
           ++ replace (Z.of_nat 3%nat) with 3%Z by reflexivity.
              assert (Hmod3 : 23%Z mod 10%Z = 3%Z) by (vm_compute; reflexivity).
              rewrite Hmod3. reflexivity.
           ++ replace (23%Z / 10%Z) with 2%Z by (vm_compute; reflexivity).
              apply (dop_step 2%Z 2%nat []).
              ** lia.
              ** split; lia.
              ** replace (Z.of_nat 2%nat) with 2%Z by reflexivity.
                 assert (Hmod4 : 2%Z mod 10%Z = 2%Z) by (vm_compute; reflexivity).
                 rewrite Hmod4. reflexivity.
              ** assert (Hdiv : 2%Z / 10%Z = 0%Z) by (apply Z.div_small; split; lia).
                 rewrite Hdiv.
                 apply dop_zero.
  - apply ceo_cons_odd.
    + simpl. reflexivity.
    + apply ceo_cons_even.
      * simpl. reflexivity.
      * apply ceo_cons_odd.
        -- simpl. reflexivity.
        -- apply ceo_cons_even.
           ++ simpl. reflexivity.
           ++ apply ceo_nil.
Qed.