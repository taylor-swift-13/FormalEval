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

Example test_sort_even_case : sort_even_spec [2; 1; 2; 3; 2] [2; 1; 2; 3; 2].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      destruct i.
      * (* i = 0 *)
        simpl in Hodd. discriminate Hodd.
      * destruct i.
        -- (* i = 1 *)
           simpl. reflexivity.
        -- destruct i.
           ++ (* i = 2 *)
              simpl in Hodd. discriminate Hodd.
           ++ destruct i.
              ** (* i = 3 *)
                 simpl. reflexivity.
              ** destruct i.
                 --- (* i = 4 *)
                     simpl in Hodd. discriminate Hodd.
                 --- (* i >= 5 *)
                     simpl in Hlen. lia.
    + split.
      * (* 3. Permutation check *)
        simpl. apply Permutation_refl.
      * (* 4. Sorted check *)
        simpl.
        apply Sorted_cons.
        -- (* Tail is sorted *)
           apply Sorted_cons.
           ++ (* Inner tail is sorted *)
              apply Sorted_cons.
              ** apply Sorted_nil.
              ** apply HdRel_nil.
           ++ (* Head relation: 2 <= 2 *)
              apply HdRel_cons.
              lia.
        -- (* Head relation: 2 <= 2 *)
           apply HdRel_cons.
           lia.
Qed.