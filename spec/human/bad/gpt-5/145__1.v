Require Import Coq.ZArith.ZArith Coq.Lists.List Coq.Arith.Arith Permutation Sorting.Sorted Lia.
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

Example problem_145_example :
  problem_145_spec [1%Z; 11%Z; -1%Z; -11%Z; -12%Z]
                   [1%Z; -1%Z; 11%Z; -11%Z; -12%Z].
Proof.
  set (indexed :=
    [(1%Z, 0%nat); (11%Z, 1%nat); (-1%Z, 2%nat); (-11%Z, 3%nat); (-12%Z, 4%nat)]).
  set (sorted_indexed :=
    [(1%Z, 0%nat); (-1%Z, 2%nat); (11%Z, 1%nat); (-11%Z, 3%nat); (-12%Z, 4%nat)]).
  exists indexed, sorted_indexed.
  split.
  - change indexed with
      ((1%Z, 0%nat) ::
       map (fun '(z, i) => (z, S i))
           [(11%Z, 0%nat); (-1%Z, 1%nat); (-11%Z, 2%nat); (-12%Z, 3%nat)]).
    constructor.
    + change [(11%Z, 0%nat); (-1%Z, 1%nat); (-11%Z, 2%nat); (-12%Z, 3%nat)] with
        ((11%Z, 0%nat) ::
         map (fun '(z, i) => (z, S i))
             [(-1%Z, 0%nat); (-11%Z, 1%nat); (-12%Z, 2%nat)]).
      constructor.
      * change [(-1%Z, 0%nat); (-11%Z, 1%nat); (-12%Z, 2%nat)] with
          ((-1%Z, 0%nat) ::
           map (fun '(z, i) => (z, S i))
               [(-11%Z, 0%nat); (-12%Z, 1%nat)]).
        constructor.
        -- change [(-11%Z, 0%nat); (-12%Z, 1%nat)] with
             ((-11%Z, 0%nat) ::
              map (fun '(z, i) => (z, S i))
                  [(-12%Z, 0%nat)]).
           constructor.
           ++ change [(-12%Z, 0%nat)] with
                ((-12%Z, 0%nat) ::
                 map (fun '(z, i) => (z, S i)) []).
              constructor.
              ** constructor.
           ++ simpl. reflexivity.
        -- simpl. reflexivity.
      * simpl. reflexivity.
    + simpl. reflexivity.
  - split.
    + simpl.
      apply Permutation_cons.
      apply Permutation_swap.
    + split.
      * assert (Hsdpos1 : sum_digits_pos_rel 1%Z 1%Z).
        { apply sdpr_step with (s_tail := 0%Z).
          - lia.
          - apply sdpr_zero.
          - vm_compute; reflexivity. }
        assert (Hsdpos11 : sum_digits_pos_rel 11%Z 2%Z).
        { apply sdpr_step with (s_tail := 1%Z).
          - lia.
          - exact Hsdpos1.
          - vm_compute; reflexivity. }
        assert (Hsdpos12 : sum_digits_pos_rel 12%Z 3%Z).
        { apply sdpr_step with (s_tail := 1%Z).
          - lia.
          - exact Hsdpos1.
          - vm_compute; reflexivity. }
        assert (Hsd_1 : sum_digits_rel 1%Z 1%Z) by (apply sdr_pos; [lia|exact Hsdpos1]).
        assert (Hsd_m1 : sum_digits_rel (-1)%Z 1%Z).
        { apply (sdr_neg (-1%Z) 1%Z 1%Z); try lia.
          - vm_compute; reflexivity.
          - exact Hsdpos1. }
        assert (Hsd_11 : sum_digits_rel 11%Z 2%Z) by (apply sdr_pos; [lia|exact Hsdpos11]).
        assert (Hsd_m11 : sum_digits_rel (-11)%Z 2%Z).
        { apply (sdr_neg (-11%Z) 2%Z 11%Z); try lia.
          - vm_compute; reflexivity.
          - exact Hsdpos11. }
        assert (Hsd_m12 : sum_digits_rel (-12)%Z 3%Z).
        { apply (sdr_neg (-12%Z) 3%Z 12%Z); try lia.
          - vm_compute; reflexivity.
          - exact Hsdpos12. }
        constructor.
        -- constructor.
           ++ apply (lsr_eq 1%Z (-1)%Z 0%nat 2%nat 1%Z); try assumption; try assumption; lia.
           ++ constructor.
              ** apply (lsr_lt 1%Z 11%Z 0%nat 1%nat 1%Z 2%Z); try assumption; lia.
              ** constructor.
                 --- apply (lsr_lt 1%Z (-11)%Z 0%nat 3%nat 1%Z 2%Z); try assumption; lia.
                 --- constructor.
                     ---- apply (lsr_lt 1%Z (-12)%Z 0%nat 4%nat 1%Z 3%Z); try assumption; lia.
                     ---- constructor.
        -- constructor.
           ++ constructor.
              ** apply (lsr_lt (-1)%Z 11%Z 2%nat 1%nat 1%Z 2%Z); try assumption; lia.
              ** constructor.
                 --- apply (lsr_lt (-1)%Z (-11)%Z 2%nat 3%nat 1%Z 2%Z); try assumption; lia.
                 --- constructor.
                     ---- apply (lsr_lt (-1)%Z (-12)%Z 2%nat 4%nat 1%Z 3%Z); try assumption; lia.
                     ---- constructor.
           ++ constructor.
              ** constructor.
                 --- apply (lsr_eq 11%Z (-11)%Z 1%nat 3%nat 2%Z); try assumption; try assumption; lia.
                 --- constructor.
                     ---- apply (lsr_lt 11%Z (-12)%Z 1%nat 4%nat 2%Z 3%Z); try assumption; lia.
                     ---- constructor.
              ** constructor.
                 --- constructor.
                     ---- apply (lsr_lt (-11)%Z (-12)%Z 3%nat 4%nat 2%Z 3%Z); try assumption; lia.
                     ---- constructor.
                 --- constructor.
      * simpl. reflexivity.
Qed.