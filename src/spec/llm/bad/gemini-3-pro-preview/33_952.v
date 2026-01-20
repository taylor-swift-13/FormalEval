Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Open Scope Z_scope.

Fixpoint extract_thirds (l : list Z) (i : nat) : list Z :=
  match l with
  | [] => []
  | x :: xs => 
      if (i mod 3 =? 0)%nat 
      then x :: extract_thirds xs (S i) 
      else extract_thirds xs (S i)
  end.

Definition sort_third_spec (l : list Z) (res : list Z) : Prop :=
  length res = length l /\
  (forall i : nat, (i mod 3 <> 0)%nat -> nth_error res i = nth_error l i) /\
  Permutation (extract_thirds res 0) (extract_thirds l 0) /\
  Sorted Z.le (extract_thirds res 0).

Example test_case : sort_third_spec 
  [300%Z; 500%Z; 6%Z; 7%Z; 290%Z; 8%Z; 289%Z; 20%Z; -105%Z; -277%Z; 104%Z; 200%Z; 3%Z; 4%Z; 700%Z; 900%Z; -901%Z; 800%Z; 1000%Z; -901%Z; -9%Z]
  [-277%Z; 500%Z; 6%Z; 3%Z; 290%Z; 8%Z; 7%Z; 20%Z; -105%Z; 289%Z; 104%Z; 200%Z; 300%Z; 4%Z; 700%Z; 900%Z; -901%Z; 800%Z; 1000%Z; -901%Z; -9%Z].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices *)
      intros i H.
      do 21 (destruct i; [
        simpl;
        try (match goal with
             | H : (_ mod 3 <> 0)%nat |- _ =>
                 exfalso; apply H; reflexivity
             end);
        reflexivity
      | ]).
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        match goal with
        | |- Permutation ?L1 ?L2 =>
          let v1 := eval vm_compute in L1 in
          let v2 := eval vm_compute in L2 in
          change L1 with v1;
          change L2 with v2
        end.
        apply Permutation_refl.
      * (* Sorted *)
        match goal with
        | |- Sorted _ ?L =>
          let v := eval vm_compute in L in
          change L with v
        end.
        repeat (apply Sorted_cons; [
          try apply HdRel_nil;
          apply HdRel_cons;
          apply Zle_bool_imp_le;
          reflexivity
        | ]).
        apply Sorted_nil.
Qed.