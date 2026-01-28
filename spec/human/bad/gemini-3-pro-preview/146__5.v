Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith Coq.micromega.Lia.
Import ListNotations.
Open Scope Z_scope.

Definition absZ (n : Z) : Z := Z.abs n.

(* 最高位与末位数字（针对非负整数） *)
Inductive last_digit_rel : Z -> Z -> Prop :=
| ld_zero : last_digit_rel 0%Z 0%Z
| ld_step : forall n d,
    0 < n -> 0 <= d < 10 -> d = n mod 10 -> last_digit_rel n d.

Inductive msd_rel : Z -> Z -> Prop :=
| msd_single : forall n, 0 <= n < 10 -> msd_rel n n
| msd_step : forall n m,
    10 <= n -> msd_rel (n / 10) m -> msd_rel n m.

(* 单个数满足：>10 且 首末位均为奇数 *)
Inductive special_number_rel : Z -> Prop :=
| sn_build : forall n d_first d_last,
    10 < n ->
    msd_rel (absZ n) d_first -> last_digit_rel (absZ n) d_last ->
    Z.odd d_first = true -> Z.odd d_last = true ->
    special_number_rel n.

(* 对列表计数：满足 special_number_rel 的元素个数 *)
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

(* 任意整数列表输入均可 *)
Definition problem_146_pre (nums : list Z) : Prop := True.

(* 规约：输出等于满足条件的元素计数（以 Z 形式给出） *)
Definition problem_146_spec (nums : list Z) (output : Z) : Prop :=
  exists k : nat, count_special_list nums k /\ output = Z.of_nat k.

Example test_case : problem_146_spec [71%Z; -2%Z; -33%Z; 75%Z; 21%Z; 19%Z] 3%Z.
Proof.
  unfold problem_146_spec.
  exists 3%nat.
  split.
  - apply csl_cons_hit.
    { (* 71 *)
      eapply sn_build.
      - lia.
      - apply msd_step with (m:=7). lia. simpl. apply msd_single. lia.
      - apply ld_step. lia. lia. reflexivity.
      - reflexivity.
      - reflexivity.
    }
    apply csl_cons_miss.
    { (* -2 *)
      intro H. inversion H; subst. lia.
    }
    apply csl_cons_miss.
    { (* -33 *)
      intro H. inversion H; subst. lia.
    }
    apply csl_cons_hit.
    { (* 75 *)
      eapply sn_build.
      - lia.
      - apply msd_step with (m:=7). lia. simpl. apply msd_single. lia.
      - apply ld_step. lia. lia. reflexivity.
      - reflexivity.
      - reflexivity.
    }
    apply csl_cons_miss.
    { (* 21 *)
      intro H. inversion H; subst.
      match goal with H: msd_rel 21 _ |- _ => inversion H; subst end.
      - lia.
      - simpl in *. match goal with H: msd_rel 2 _ |- _ => inversion H; subst end.
        + simpl in *. discriminate.
        + lia.
    }
    apply csl_cons_hit.
    { (* 19 *)
      eapply sn_build.
      - lia.
      - apply msd_step with (m:=1). lia. simpl. apply msd_single. lia.
      - apply ld_step. lia. lia. reflexivity.
      - reflexivity.
      - reflexivity.
    }
    apply csl_nil.
  - simpl. reflexivity.
Qed.