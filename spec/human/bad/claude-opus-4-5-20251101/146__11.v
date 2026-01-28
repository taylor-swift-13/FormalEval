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

Lemma msd_101 : msd_rel 101 1.
Proof.
  apply msd_step. lia.
  apply msd_step. lia.
  simpl. apply msd_single. lia.
Qed.

Lemma last_digit_101 : last_digit_rel 101 1.
Proof.
  apply ld_step with (n := 101) (d := 1).
  - lia.
  - lia.
  - reflexivity.
Qed.

Lemma special_101 : special_number_rel 101.
Proof.
  apply sn_build with (d_first := 1) (d_last := 1).
  - lia.
  - simpl. exact msd_101.
  - simpl. exact last_digit_101.
  - reflexivity.
  - reflexivity.
Qed.

Lemma not_special_neg35 : ~ special_number_rel (-35).
Proof.
  intro H.
  inversion H.
  lia.
Qed.

Lemma not_special_16 : ~ special_number_rel 16.
Proof.
  intro H.
  inversion H.
  lia.
Qed.

Lemma not_special_44 : ~ special_number_rel 44.
Proof.
  intro H.
  inversion H.
  lia.
Qed.

Lemma not_special_neg67 : ~ special_number_rel (-67).
Proof.
  intro H.
  inversion H.
  lia.
Qed.

Example test_problem_146 : problem_146_spec [101%Z; -35%Z; 16%Z; 44%Z; -67%Z] 1%Z.
Proof.
  unfold problem_146_spec.
  exists 1%nat.
  split.
  - apply csl_cons_hit.
    + exact special_101.
    + apply csl_cons_miss.
      * exact not_special_neg35.
      * apply csl_cons_miss.
        -- exact not_special_16.
        -- apply csl_cons_miss.
           ++ exact not_special_44.
           ++ apply csl_cons_miss.
              ** exact not_special_neg67.
              ** apply csl_nil.
  - reflexivity.
Qed.