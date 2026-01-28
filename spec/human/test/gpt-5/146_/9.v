Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Definition absZ (n : Z) : Z := Z.abs n.

Inductive last_digit_rel : Z -> Z -> Prop :=
| ld_zero : last_digit_rel 0%Z 0%Z
| ld_step : forall n d,
    0 < n -> 0 <= d < 10 -> d = n mod 10 -> last_digit_rel n d.

Inductive msd_rel : Z -> Z -> Prop :=
| msd_single : forall n, 0 <= n < 10 -> msd_rel n n
| msd_step : forall n m,
    10 <= n -> msd_rel (n / 10) m -> msd_rel n m.

Inductive special_number_rel : Z -> Prop :=
| sn_build : forall n d_first d_last,
    10 < n ->
    msd_rel (absZ n) d_first -> last_digit_rel (absZ n) d_last ->
    Z.odd d_first = true -> Z.odd d_last = true ->
    special_number_rel n.

Inductive count_special_list : list Z -> nat -> Prop :=
| csl_nil : count_special_list [] 0%nat
| csl_cons_hit : forall h t k,
    special_number_rel h ->
    count_special_list t k ->
    count_special_list (h :: t) (S k)
| csl_cons_miss : forall h t k,
    ~ special_number_rel h ->
    count_special_list t k ->
    count_special_list (h :: t) k.

Definition problem_146_pre (nums : list Z) : Prop := True.

Definition problem_146_spec (nums : list Z) (output : Z) : Prop :=
  exists k : nat, count_special_list nums k /\ output = Z.of_nat k.

Example test_case_problem_146_1 :
  problem_146_spec [57%Z; -23%Z; -15%Z; 42%Z; 99%Z; 104%Z] 2%Z.
Proof.
  unfold problem_146_spec.
  exists 2%nat.
  split.
  - apply csl_cons_hit.
    + apply sn_build with (d_first := 5%Z) (d_last := 7%Z).
      * lia.
      * simpl. apply msd_step.
        -- lia.
        -- assert (Hdiv57 : 57 / 10 = 5%Z) by (vm_compute; reflexivity).
           rewrite Hdiv57.
           apply msd_single; lia.
      * simpl. apply ld_step.
        -- lia.
        -- lia.
        -- vm_compute; reflexivity.
      * simpl; reflexivity.
      * simpl; reflexivity.
    + apply csl_cons_miss.
      * intro H; inversion H; lia.
      * apply csl_cons_miss.
        -- intro H; inversion H; lia.
        -- apply csl_cons_miss.
           ++ intro H.
              inversion H as [n d_first d_last Hn Hmsd Hld Hodd_first Hodd_last].
              simpl in Hld.
              inversion Hld as [ | n0 d0 Hn0 Hd_bound Heq].
              simpl in Heq.
              vm_compute in Heq.
              rewrite Heq in Hodd_last.
              vm_compute in Hodd_last.
              discriminate.
           ++ apply csl_cons_hit.
              ** apply sn_build with (d_first := 9%Z) (d_last := 9%Z).
                 --- lia.
                 --- simpl. apply msd_step.
                     +++ lia.
                     +++ assert (Hdiv99 : 99 / 10 = 9%Z) by (vm_compute; reflexivity).
                         rewrite Hdiv99.
                         apply msd_single; lia.
                 --- simpl. apply ld_step.
                     +++ lia.
                     +++ lia.
                     +++ vm_compute; reflexivity.
                 --- simpl; reflexivity.
                 --- simpl; reflexivity.
              ** apply csl_cons_miss.
                 --- intro H.
                     inversion H as [n d_first d_last Hn Hmsd Hld Hodd_first Hodd_last].
                     simpl in Hld.
                     inversion Hld as [ | n0 d0 Hn0 Hd_bound Heq].
                     simpl in Heq.
                     vm_compute in Heq.
                     rewrite Heq in Hodd_last.
                     vm_compute in Hodd_last.
                     discriminate.
                 --- apply csl_nil.
  - simpl; reflexivity.
Qed.