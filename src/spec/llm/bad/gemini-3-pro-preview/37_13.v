Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Import ListNotations.
Open Scope Z_scope.

Fixpoint get_evens (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: tl => x :: get_evens tl
  end.

Definition sort_even_spec (l res : list Z) : Prop :=
  length l = length res /\
  (forall i : nat, (i < length l)%nat -> Nat.odd i = true -> nth i l 0 = nth i res 0) /\
  Permutation (get_evens l) (get_evens res) /\
  Sorted Z.le (get_evens res).

Example test_sort_even_case : sort_even_spec [0; 0; 0; -1; -1; -1; 2; 2; 2] [-1; 0; 0; -1; 0; -1; 2; 2; 2].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      destruct i. { simpl. reflexivity. }
      destruct i. { simpl in Hodd. discriminate Hodd. }
      simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* [0; 0; -1; 2; 2] ~ [-1; 0; 0; 2; 2] *)
        transitivity (0 :: -1 :: 0 :: 2 :: 2).
        -- apply Permutation_cons. apply perm_swap.
        -- apply perm_swap.
      * (* 4. Sorted check *)
        simpl.
        apply Sorted_cons.
        { (* Sorted [0; 0; 2; 2] *)
          apply Sorted_cons.
          { (* Sorted [0; 2; 2] *)
            apply Sorted_cons.
            { (* Sorted [2; 2] *)
              apply Sorted_cons.
              { (* Sorted [2] *)
                apply Sorted_cons.
                { apply Sorted_nil. }
                { apply HdRel_nil. }
              }
              { (* HdRel 2 [2] *) apply HdRel_cons. lia. }
            }
            { (* HdRel 0 [2; 2] *) apply HdRel_cons. lia. }
          }
          { (* HdRel 0 [0; 2; 2] *) apply HdRel_cons. lia. }
        }
        { (* HdRel -1 [0; 0; 2; 2] *) apply HdRel_cons. lia. }
Qed.