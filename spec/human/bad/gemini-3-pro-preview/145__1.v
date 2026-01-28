Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith Permutation Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.

Inductive sum_digits_pos_rel : Z -> Z -> Prop :=
| sdpr_zero : sum_digits_pos_rel 0%Z 0%Z
| sdpr_step : forall n s s_tail, 0 < n -> sum_digits_pos_rel (n / 10) s_tail ->
   s = (n mod 10) + s_tail -> sum_digits_pos_rel n s.

Inductive sum_digits_rel : Z -> Z -> Prop :=
| sdr_zero : sum_digits_rel 0%Z 0%Z
| sdr_pos : forall n s, 0 < n -> sum_digits_pos_rel n s -> sum_digits_rel n s
| sdr_neg : forall n s p, n < 0 -> p = Z.abs n -> sum_digits_pos_rel p s ->
   sum_digits_rel n s.

Inductive le_stable_rel : (Z * nat) -> (Z * nat) -> Prop :=
| lsr_lt : forall z1 z2 (idx1 idx2 : nat) s1 s2,
   sum_digits_rel z1 s1 -> sum_digits_rel z2 s2 -> s1 < s2 ->
   le_stable_rel (z1, idx1) (z2, idx2)
| lsr_eq : forall z1 z2 (idx1 idx2 : nat) s,
   sum_digits_rel z1 s -> sum_digits_rel z2 s -> Nat.le idx1 idx2 ->
   le_stable_rel (z1, idx1) (z2, idx2).

Inductive indexed_list_rel : list Z -> list (Z * nat) -> Prop :=
| ilr_nil : indexed_list_rel nil nil
| ilr_cons : forall h t indexed_tail, indexed_list_rel t indexed_tail ->
    indexed_list_rel (h :: t) ((h, 0%nat) :: map (fun '(z, i) => (z, S i)) indexed_tail).

Inductive sorted_stable_rel : list (Z * nat) -> list (Z * nat) -> Prop :=
| ssr_nil : sorted_stable_rel nil nil
| ssr_single : forall p, sorted_stable_rel (p :: nil) (p :: nil)
| ssr_cons : forall p ps sorted_tail, le_stable_rel (hd (0%Z, 0%nat) sorted_tail) p ->
    sorted_stable_rel ps sorted_tail ->
    sorted_stable_rel (p :: ps) (p :: sorted_tail).

Definition problem_145_pre (l_in : list Z) : Prop := True.

Definition problem_145_spec (l_in : list Z) (l_out : list Z) : Prop :=
  exists indexed sorted_indexed, indexed_list_rel l_in indexed /\
    Permutation indexed sorted_indexed /\
    Sorted le_stable_rel sorted_indexed /\
    l_out = map fst sorted_indexed.

Example problem_145_example : problem_145_spec [1; 11; -1; -11; -12] [1; -1; 11; -11; -12].
Proof.
  unfold problem_145_spec.
  exists [(1, 0%nat); (11, 1%nat); (-1, 2%nat); (-11, 3%nat); (-12, 4%nat)].
  exists [(1, 0%nat); (-1, 2%nat); (11, 1%nat); (-11, 3%nat); (-12, 4%nat)].
  split.
  - (* indexed_list_rel *)
    repeat constructor.
  - split.
    + (* Permutation *)
      apply Permutation_cons.
      apply Permutation_swap.
    + split.
      * (* Sorted *)
        apply Sorted_cons.
        { apply HdRel_cons. apply lsr_eq with (s:=1).
          - apply sdr_pos; [lia|]. apply sdpr_step with (s_tail:=0); [lia|constructor|reflexivity].
          - apply sdr_neg with (p:=1); [lia|reflexivity|]. apply sdpr_step with (s_tail:=0); [lia|constructor|reflexivity].
          - lia. }
        apply Sorted_cons.
        { apply HdRel_cons. apply lsr_lt with (s1:=1) (s2:=2).
          - apply sdr_neg with (p:=1); [lia|reflexivity|]. apply sdpr_step with (s_tail:=0); [lia|constructor|reflexivity].
          - apply sdr_pos; [lia|]. apply sdpr_step with (s_tail:=1); [lia| |reflexivity]. apply sdpr_step with (s_tail:=0); [lia|constructor|reflexivity].
          - lia. }
        apply Sorted_cons.
        { apply HdRel_cons. apply lsr_eq with (s:=2).
          - apply sdr_pos; [lia|]. apply sdpr_step with (s_tail:=1); [lia| |reflexivity]. apply sdpr_step with (s_tail:=0); [lia|constructor|reflexivity].
          - apply sdr_neg with (p:=11); [lia|reflexivity|]. apply sdpr_step with (s_tail:=1); [lia| |reflexivity]. apply sdpr_step with (s_tail:=0); [lia|constructor|reflexivity].
          - lia. }
        apply Sorted_cons.
        { apply HdRel_cons. apply lsr_lt with (s1:=2) (s2:=3).
          - apply sdr_neg with (p:=11); [lia|reflexivity|]. apply sdpr_step with (s_tail:=1); [lia| |reflexivity]. apply sdpr_step with (s_tail:=0); [lia|constructor|reflexivity].
          - apply sdr_neg with (p:=12); [lia|reflexivity|]. apply sdpr_step with (s_tail:=1); [lia| |reflexivity]. apply sdpr_step with (s_tail:=0); [lia|constructor|reflexivity].
          - lia. }
        apply Sorted_nil.
      * (* map *)
        reflexivity.
Qed.