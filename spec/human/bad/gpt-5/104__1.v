(* 导入所需的基础库 *)
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.

Import ListNotations.

(* 辅助定义：判断单个数字是否为奇数 *)
Definition is_odd_digit (d : nat) : Prop :=
  d = 1 \/ d = 3 \/ d = 5 \/ d = 7 \/ d = 9.

Inductive all_digits_odd_list_rel : list nat -> Prop :=
  | adolr_nil : all_digits_odd_list_rel []
  | adolr_cons : forall h t,
      is_odd_digit h ->
      all_digits_odd_list_rel t ->
      all_digits_odd_list_rel (h :: t).

Inductive nat_to_digits_rel : nat -> list nat -> Prop :=
  | ntdr_zero : nat_to_digits_rel 0 []
  | ntdr_step : forall n d rest,
      n > 0 ->
      d = n mod 10 ->
      nat_to_digits_rel (n / 10) rest ->
      nat_to_digits_rel n (d :: rest).

Inductive has_only_odd_digits_rel : nat -> Prop :=
  | hodd_base : forall n digits,
      n > 0 ->
      nat_to_digits_rel n digits ->
      all_digits_odd_list_rel digits ->
      has_only_odd_digits_rel n.

Inductive filter_odd_digits_rel : list nat -> list nat -> Prop :=
  | fodr_nil : filter_odd_digits_rel [] []
  | fodr_keep : forall h t result,
      has_only_odd_digits_rel h ->
      filter_odd_digits_rel t result ->
      filter_odd_digits_rel (h :: t) (h :: result)
  | fodr_drop : forall h t result,
      ~ has_only_odd_digits_rel h ->
      filter_odd_digits_rel t result ->
      filter_odd_digits_rel (h :: t) result.

Inductive insert_sorted_rel : nat -> list nat -> list nat -> Prop :=
  | isr_nil : forall x, insert_sorted_rel x [] [x]
  | isr_insert : forall x h t,
      (x <= h)%nat ->
      insert_sorted_rel x (h :: t) (x :: h :: t)
  | isr_skip : forall x h t result,
      (x > h)%nat ->
      insert_sorted_rel x t result ->
      insert_sorted_rel x (h :: t) (h :: result).

Inductive sort_list_rel : list nat -> list nat -> Prop :=
  | slr_nil : sort_list_rel [] []
  | slr_cons : forall h t sorted_tail result,
      sort_list_rel t sorted_tail ->
      insert_sorted_rel h sorted_tail result ->
      sort_list_rel (h :: t) result.

Definition problem_104_pre (x : list nat) : Prop := Forall (fun n => n > 0) x.

Definition problem_104_spec (x y : list nat) : Prop :=
  (forall n, In n x -> n > 0) /\
  exists filtered,
    filter_odd_digits_rel x filtered /\
    sort_list_rel filtered y.

(* Helper lemmas about odd digits *)
Lemma is_odd_digit_1 : is_odd_digit 1.
Proof. left; reflexivity. Qed.

Lemma is_odd_digit_3 : is_odd_digit 3.
Proof. right; left; reflexivity. Qed.

Lemma is_odd_digit_5 : is_odd_digit 5.
Proof. right; right; left; reflexivity. Qed.

Lemma is_not_odd_digit_2 : ~ is_odd_digit 2.
Proof.
  intros H. destruct H as [H|[H|[H|[H|H]]]]; congruence.
Qed.

(* Concrete digit decompositions *)
Lemma nat_to_digits_1 : nat_to_digits_rel 1 [1].
Proof.
  eapply ntdr_step with (d:=1) (rest:=[]).
  - lia.
  - vm_compute; reflexivity.
  - replace (1 / 10) with 0 by vm_compute.
    apply ntdr_zero.
Qed.

Lemma nat_to_digits_3 : nat_to_digits_rel 3 [3].
Proof.
  eapply ntdr_step with (d:=3) (rest:=[]).
  - lia.
  - vm_compute; reflexivity.
  - replace (3 / 10) with 0 by vm_compute.
    apply ntdr_zero.
Qed.

Lemma nat_to_digits_15 : nat_to_digits_rel 15 [5;1].
Proof.
  eapply ntdr_step with (d:=5) (rest:=[1]).
  - lia.
  - vm_compute; reflexivity.
  - replace (15 / 10) with 1 by vm_compute.
    apply nat_to_digits_1.
Qed.

Lemma nat_to_digits_33 : nat_to_digits_rel 33 [3;3].
Proof.
  eapply ntdr_step with (d:=3) (rest:=[3]).
  - lia.
  - vm_compute; reflexivity.
  - replace (33 / 10) with 3 by vm_compute.
    eapply ntdr_step with (d:=3) (rest:=[]).
    + lia.
    + vm_compute; reflexivity.
    + replace (3 / 10) with 0 by vm_compute.
      apply ntdr_zero.
Qed.

Lemma nat_to_digits_1422 : nat_to_digits_rel 1422 [2;2;4;1].
Proof.
  eapply ntdr_step with (d:=2) (rest:=[2;4;1]).
  - lia.
  - vm_compute; reflexivity.
  - replace (1422 / 10) with 142 by vm_compute.
    eapply ntdr_step with (d:=2) (rest:=[4;1]).
    + lia.
    + vm_compute; reflexivity.
    + replace (142 / 10) with 14 by vm_compute.
      eapply ntdr_step with (d:=4) (rest:=[1]).
      * lia.
      * vm_compute; reflexivity.
      * replace (14 / 10) with 1 by vm_compute.
        apply nat_to_digits_1.
Qed.

(* All-digits-odd proofs for specific lists *)
Lemma all_digits_odd_list_rel_1 : all_digits_odd_list_rel [1].
Proof.
  apply adolr_cons; [apply is_odd_digit_1|apply adolr_nil].
Qed.

Lemma all_digits_odd_list_rel_5_1 : all_digits_odd_list_rel [5;1].
Proof.
  apply adolr_cons; [apply is_odd_digit_5|].
  apply adolr_cons; [apply is_odd_digit_1|].
  apply adolr_nil.
Qed.

Lemma all_digits_odd_list_rel_3_3 : all_digits_odd_list_rel [3;3].
Proof.
  apply adolr_cons; [apply is_odd_digit_3|].
  apply adolr_cons; [apply is_odd_digit_3|].
  apply adolr_nil.
Qed.

(* Has-only-odd-digits proofs for specific numbers *)
Lemma has_only_odd_digits_rel_1 : has_only_odd_digits_rel 1.
Proof.
  eapply hodd_base with (digits := [1]).
  - lia.
  - apply nat_to_digits_1.
  - apply all_digits_odd_list_rel_1.
Qed.

Lemma has_only_odd_digits_rel_15 : has_only_odd_digits_rel 15.
Proof.
  eapply hodd_base with (digits := [5;1]).
  - lia.
  - apply nat_to_digits_15.
  - apply all_digits_odd_list_rel_5_1.
Qed.

Lemma has_only_odd_digits_rel_33 : has_only_odd_digits_rel 33.
Proof.
  eapply hodd_base with (digits := [3;3]).
  - lia.
  - apply nat_to_digits_33.
  - apply all_digits_odd_list_rel_3_3.
Qed.

(* Not has-only-odd-digits for 1422 *)
Lemma not_has_only_odd_digits_1422 : ~ has_only_odd_digits_rel 1422.
Proof.
  intros H.
  inversion H as [n digits Hpos Hdigits Hall]; subst n.
  inversion Hdigits; subst.
  - lia.
  - inversion Hall; subst.
    assert (Hmod : 1422 mod 10 = 2) by (vm_compute; reflexivity).
    rewrite H0 in H2. rewrite Hmod in H2.
    apply is_not_odd_digit_2 in H2.
    contradiction.
Qed.

Example problem_104_example :
  problem_104_spec [15; 33; 1422; 1] [1; 15; 33].
Proof.
  unfold problem_104_spec.
  split.
  - intros n HIn.
    simpl in HIn.
    destruct HIn as [->|HIn]; [lia|].
    destruct HIn as [->|HIn]; [lia|].
    destruct HIn as [->|HIn]; [lia|].
    destruct HIn as [->|HIn]; [lia|].
    inversion HIn.
  - exists [15; 33; 1].
    split.
    + (* filter_odd_digits_rel *)
      apply fodr_keep; [apply has_only_odd_digits_rel_15|].
      apply fodr_keep; [apply has_only_odd_digits_rel_33|].
      apply fodr_drop; [apply not_has_only_odd_digits_1422|].
      apply fodr_keep; [apply has_only_odd_digits_rel_1|].
      apply fodr_nil.
    + (* sort_list_rel *)
      (* sort [15;33;1] -> [1;15;33] *)
      eapply slr_cons with (sorted_tail := [1;33]) (result := [1;15;33]).
      * (* sort [33;1] -> [1;33] *)
        eapply slr_cons with (sorted_tail := [1]) (result := [1;33]).
        -- (* sort [1] -> [1] *)
           eapply slr_cons with (sorted_tail := []) (result := [1]).
           ++ apply slr_nil.
           ++ apply isr_nil.
        -- (* insert 33 into [1] -> [1;33] *)
           apply isr_skip with (result := [33]).
           ++ lia.
           ++ apply isr_nil.
      * (* insert 15 into [1;33] -> [1;15;33] *)
        apply isr_skip with (result := [15;33]).
        -- lia.
        -- apply isr_insert; lia.
Qed.