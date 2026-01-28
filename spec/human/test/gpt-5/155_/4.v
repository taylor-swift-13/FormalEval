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

Example even_odd_count_test_346211 :
  problem_155_spec 346211%Z (3%nat, 3%nat).
Proof.
  unfold problem_155_spec.
  simpl.
  exists [1%nat; 1%nat; 2%nat; 6%nat; 4%nat; 3%nat].
  split.
  - apply doz_pos.
    + lia.
    + apply (dop_step 346211%Z 1%nat [1%nat; 2%nat; 6%nat; 4%nat; 3%nat]).
      * lia.
      * split; lia.
      * replace (Z.of_nat 1%nat) with 1%Z by reflexivity.
        vm_compute. reflexivity.
      * assert (Hdiv1 : 346211%Z / 10%Z = 34621%Z) by (vm_compute; reflexivity).
        rewrite Hdiv1.
        apply (dop_step 34621%Z 1%nat [2%nat; 6%nat; 4%nat; 3%nat]).
        -- lia.
        -- split; lia.
        -- replace (Z.of_nat 1%nat) with 1%Z by reflexivity.
           vm_compute. reflexivity.
        -- assert (Hdiv2 : 34621%Z / 10%Z = 3462%Z) by (vm_compute; reflexivity).
           rewrite Hdiv2.
           apply (dop_step 3462%Z 2%nat [6%nat; 4%nat; 3%nat]).
           --- lia.
           --- split; lia.
           --- replace (Z.of_nat 2%nat) with 2%Z by reflexivity.
               vm_compute. reflexivity.
           --- assert (Hdiv3 : 3462%Z / 10%Z = 346%Z) by (vm_compute; reflexivity).
               rewrite Hdiv3.
               apply (dop_step 346%Z 6%nat [4%nat; 3%nat]).
               ---- lia.
               ---- split; lia.
               ---- replace (Z.of_nat 6%nat) with 6%Z by reflexivity.
                    vm_compute. reflexivity.
               ---- assert (Hdiv4 : 346%Z / 10%Z = 34%Z) by (vm_compute; reflexivity).
                    rewrite Hdiv4.
                    apply (dop_step 34%Z 4%nat [3%nat]).
                    ----- lia.
                    ----- split; lia.
                    ----- replace (Z.of_nat 4%nat) with 4%Z by reflexivity.
                          vm_compute. reflexivity.
                    ----- assert (Hdiv5 : 34%Z / 10%Z = 3%Z) by (vm_compute; reflexivity).
                          rewrite Hdiv5.
                          apply (dop_step 3%Z 3%nat []).
                          ------ lia.
                          ------ split; lia.
                          ------ replace (Z.of_nat 3%nat) with 3%Z by reflexivity.
                                 vm_compute. reflexivity.
                          ------ assert (Hdiv6 : 3%Z / 10%Z = 0%Z) by (vm_compute; reflexivity).
                                 rewrite Hdiv6.
                                 apply dop_zero.
  - apply ceo_cons_odd.
    + simpl. reflexivity.
    + apply ceo_cons_odd.
      * simpl. reflexivity.
      * apply ceo_cons_even.
        -- simpl. reflexivity.
        -- apply ceo_cons_even.
           ++ simpl. reflexivity.
           ++ apply ceo_cons_even.
              ** simpl. reflexivity.
              ** apply ceo_cons_odd.
                 *** simpl. reflexivity.
                 *** apply ceo_nil.
Qed.