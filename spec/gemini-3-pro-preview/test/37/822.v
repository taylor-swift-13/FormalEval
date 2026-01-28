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

Example test_sort_even_case : sort_even_spec [-5; 2; 2; -7; -11; 2; 1; -5] [-11; 2; -5; -7; 1; 2; 2; -5].
Proof.
  unfold sort_even_spec.
  split.
  - (* 1. Length check *)
    simpl. reflexivity.
  - split.
    + (* 2. Odd indices check *)
      intros i Hlen Hodd.
      destruct i; [ simpl in Hodd; discriminate | ]. (* 0 *)
      destruct i; [ simpl; reflexivity | ].          (* 1 *)
      destruct i; [ simpl in Hodd; discriminate | ]. (* 2 *)
      destruct i; [ simpl; reflexivity | ].          (* 3 *)
      destruct i; [ simpl in Hodd; discriminate | ]. (* 4 *)
      destruct i; [ simpl; reflexivity | ].          (* 5 *)
      destruct i; [ simpl in Hodd; discriminate | ]. (* 6 *)
      destruct i; [ simpl; reflexivity | ].          (* 7 *)
      simpl in Hlen. lia.                            (* >= 8 *)
    + split.
      * (* 3. Permutation check *)
        simpl.
        (* Current: [-5; 2; -11; 1] *)
        (* Target:  [-11; -5; 1; 2] *)
        eapply perm_trans.
        { apply perm_skip. apply perm_swap. } (* -> [-5; -11; 2; 1] *)
        eapply perm_trans.
        { apply perm_swap. }                  (* -> [-11; -5; 2; 1] *)
        apply perm_skip. apply perm_skip. apply perm_swap. (* -> [-11; -5; 1; 2] *)
      * (* 4. Sorted check *)
        simpl.
        apply Sorted_cons.
        { apply Sorted_cons.
          { apply Sorted_cons.
            { apply Sorted_cons.
              { apply Sorted_nil. }
              { apply HdRel_nil. } }
            { apply HdRel_cons. lia. } }
          { apply HdRel_cons. lia. } }
        { apply HdRel_cons. lia. }
Qed.