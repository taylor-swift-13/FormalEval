Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Lia.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count_set_bits_pos (p : positive) : nat :=
  match p with
  | xH => 1%nat
  | xO p' => count_set_bits_pos p'
  | xI p' => S (count_set_bits_pos p')
  end.

Definition count_set_bits (z : Z) : nat :=
  match z with
  | Z0 => 0%nat
  | Zpos p => count_set_bits_pos p
  | Zneg p => count_set_bits_pos p
  end.

Definition sort_criteria (x y : Z) : Prop :=
  let cx := count_set_bits x in
  let cy := count_set_bits y in
  (cx < cy)%nat \/ (cx = cy /\ x <= y).

Definition sort_array_spec (arr : list Z) (res : list Z) : Prop :=
  Permutation arr res /\ StronglySorted sort_criteria res.

(* Let's compute the bit counts:
   1 = 1 in binary -> 1 bit
   2 = 10 in binary -> 1 bit
   3 = 11 in binary -> 2 bits
   4 = 100 in binary -> 1 bit
   5 = 101 in binary -> 2 bits
   
   So sorted by bits, then by value:
   1 bit: 1, 2, 4
   2 bits: 3, 5
   Result: [1; 2; 4; 3; 5]
*)

Example test_sort_array :
  sort_array_spec [1%Z; 5%Z; 2%Z; 3%Z; 4%Z] [1%Z; 2%Z; 4%Z; 3%Z; 5%Z].
Proof.
  unfold sort_array_spec.
  split.
  - (* Permutation proof *)
    apply perm_trans with [1%Z; 2%Z; 5%Z; 3%Z; 4%Z].
    + apply perm_skip.
      apply perm_swap.
    + apply perm_trans with [1%Z; 2%Z; 3%Z; 5%Z; 4%Z].
      * apply perm_skip. apply perm_skip.
        apply perm_swap.
      * apply perm_trans with [1%Z; 2%Z; 3%Z; 4%Z; 5%Z].
        -- apply perm_skip. apply perm_skip. apply perm_skip.
           apply perm_swap.
        -- apply perm_trans with [1%Z; 2%Z; 4%Z; 3%Z; 5%Z].
           ++ apply perm_skip. apply perm_skip.
              apply perm_swap.
           ++ apply Permutation_refl.
  - (* StronglySorted proof *)
    unfold sort_criteria.
    (* Build StronglySorted for [1; 2; 4; 3; 5] *)
    apply SSorted_cons.
    + apply SSorted_cons.
      * apply SSorted_cons.
        -- apply SSorted_cons.
           ++ apply SSorted_cons.
              ** apply SSorted_nil.
              ** apply Forall_nil.
           ++ apply Forall_cons.
              ** (* 3 <= 5: same bits (2), 3 <= 5 *)
                 right. simpl. split; [reflexivity | lia].
              ** apply Forall_nil.
        -- apply Forall_cons.
           ++ (* 4 < 3 in bits? 4 has 1 bit, 3 has 2 bits, so 1 < 2 *)
              left. simpl. lia.
           ++ apply Forall_cons.
              ** (* 4 < 5 in bits? 4 has 1 bit, 5 has 2 bits, so 1 < 2 *)
                 left. simpl. lia.
              ** apply Forall_nil.
      * apply Forall_cons.
        -- (* 2 <= 4: same bits (1), 2 <= 4 *)
           right. simpl. split; [reflexivity | lia].
        -- apply Forall_cons.
           ++ (* 2 < 3 in bits? 2 has 1 bit, 3 has 2 bits *)
              left. simpl. lia.
           ++ apply Forall_cons.
              ** (* 2 < 5 in bits? 2 has 1 bit, 5 has 2 bits *)
                 left. simpl. lia.
              ** apply Forall_nil.
    + apply Forall_cons.
      * (* 1 <= 2: same bits (1), 1 <= 2 *)
        right. simpl. split; [reflexivity | lia].
      * apply Forall_cons.
        -- (* 1 <= 4: same bits (1), 1 <= 4 *)
           right. simpl. split; [reflexivity | lia].
        -- apply Forall_cons.
           ++ (* 1 < 3 in bits? 1 has 1 bit, 3 has 2 bits *)
              left. simpl. lia.
           ++ apply Forall_cons.
              ** (* 1 < 5 in bits? 1 has 1 bit, 5 has 2 bits *)
                 left. simpl. lia.
              ** apply Forall_nil.
Qed.