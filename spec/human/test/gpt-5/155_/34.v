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

Example even_odd_count_test_neg_123456790 :
  problem_155_spec (-123456790)%Z (4%nat, 5%nat).
Proof.
  unfold problem_155_spec.
  simpl.
  exists [0%nat; 9%nat; 7%nat; 6%nat; 5%nat; 4%nat; 3%nat; 2%nat; 1%nat].
  split.
  - apply doz_neg.
    + lia.
    + replace (absZ (-123456790)%Z) with 123456790%Z by (vm_compute; reflexivity).
      apply (dop_step 123456790%Z 0%nat [9%nat; 7%nat; 6%nat; 5%nat; 4%nat; 3%nat; 2%nat; 1%nat]).
      * lia.
      * split; lia.
      * replace (Z.of_nat 0%nat) with 0%Z by reflexivity.
        vm_compute.
        reflexivity.
      * assert (Hdiv0 : 123456790%Z / 10%Z = 12345679%Z) by (vm_compute; reflexivity).
        rewrite Hdiv0.
        apply (dop_step 12345679%Z 9%nat [7%nat; 6%nat; 5%nat; 4%nat; 3%nat; 2%nat; 1%nat]).
        -- lia.
        -- split; lia.
        -- replace (Z.of_nat 9%nat) with 9%Z by reflexivity.
           vm_compute.
           reflexivity.
        -- assert (Hdiv1 : 12345679%Z / 10%Z = 1234567%Z) by (vm_compute; reflexivity).
           rewrite Hdiv1.
           apply (dop_step 1234567%Z 7%nat [6%nat; 5%nat; 4%nat; 3%nat; 2%nat; 1%nat]).
           ** lia.
           ** split; lia.
           ** replace (Z.of_nat 7%nat) with 7%Z by reflexivity.
              vm_compute.
              reflexivity.
           ** assert (Hdiv2 : 1234567%Z / 10%Z = 123456%Z) by (vm_compute; reflexivity).
              rewrite Hdiv2.
              apply (dop_step 123456%Z 6%nat [5%nat; 4%nat; 3%nat; 2%nat; 1%nat]).
              --- lia.
              --- split; lia.
              --- replace (Z.of_nat 6%nat) with 6%Z by reflexivity.
                  vm_compute.
                  reflexivity.
              --- assert (Hdiv3 : 123456%Z / 10%Z = 12345%Z) by (vm_compute; reflexivity).
                  rewrite Hdiv3.
                  apply (dop_step 12345%Z 5%nat [4%nat; 3%nat; 2%nat; 1%nat]).
                  +++ lia.
                  +++ split; lia.
                  +++ replace (Z.of_nat 5%nat) with 5%Z by reflexivity.
                      vm_compute.
                      reflexivity.
                  +++ assert (Hdiv4 : 12345%Z / 10%Z = 1234%Z) by (vm_compute; reflexivity).
                      rewrite Hdiv4.
                      apply (dop_step 1234%Z 4%nat [3%nat; 2%nat; 1%nat]).
                      *** lia.
                      *** split; lia.
                      *** replace (Z.of_nat 4%nat) with 4%Z by reflexivity.
                          vm_compute.
                          reflexivity.
                      *** assert (Hdiv5 : 1234%Z / 10%Z = 123%Z) by (vm_compute; reflexivity).
                          rewrite Hdiv5.
                          apply (dop_step 123%Z 3%nat [2%nat; 1%nat]).
                          ---- lia.
                          ---- split; lia.
                          ---- replace (Z.of_nat 3%nat) with 3%Z by reflexivity.
                               vm_compute.
                               reflexivity.
                          ---- assert (Hdiv6 : 123%Z / 10%Z = 12%Z) by (vm_compute; reflexivity).
                               rewrite Hdiv6.
                               apply (dop_step 12%Z 2%nat [1%nat]).
                               ++++ lia.
                               ++++ split; lia.
                               ++++ replace (Z.of_nat 2%nat) with 2%Z by reflexivity.
                                    vm_compute.
                                    reflexivity.
                               ++++ assert (Hdiv7 : 12%Z / 10%Z = 1%Z) by (vm_compute; reflexivity).
                                    rewrite Hdiv7.
                                    apply (dop_step 1%Z 1%nat []).
                                    **** lia.
                                    **** split; lia.
                                    **** replace (Z.of_nat 1%nat) with 1%Z by reflexivity.
                                         symmetry.
                                         apply Z.mod_small; split; lia.
                                    **** assert (Hdiv8 : 1%Z / 10%Z = 0%Z) by (apply Z.div_small; split; lia).
                                         rewrite Hdiv8.
                                         apply dop_zero.
  - apply ceo_cons_even.
    + simpl. reflexivity.
    + apply ceo_cons_odd.
      * simpl. reflexivity.
      * apply ceo_cons_odd.
        -- simpl. reflexivity.
        -- apply ceo_cons_even.
           ** simpl. reflexivity.
           ** apply ceo_cons_odd.
              *** simpl. reflexivity.
              *** apply ceo_cons_even.
                  **** simpl. reflexivity.
                  **** apply ceo_cons_odd.
                      ***** simpl. reflexivity.
                      ***** apply ceo_cons_even.
                            ****** simpl. reflexivity.
                            ****** apply ceo_cons_odd.
                                   ******** simpl. reflexivity.
                                   ******** apply ceo_nil.
Qed.