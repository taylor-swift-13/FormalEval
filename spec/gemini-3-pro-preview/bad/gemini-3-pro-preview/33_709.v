Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Micromega.Lia.
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
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 200; 3; 4; 5; 700; -104; -200; -104; -901; 800; 1000]
  [-901; 500; 6; -104; 8; 289; 4; -105; -277; 7; 200; 3; 20; 5; 700; 104; -200; -104; 300; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - simpl. reflexivity.
  - split.
    + intros i H.
      (* Check indices 0 to 21 individually *)
      do 22 (destruct i as [|i]; [
        simpl in H; try congruence; simpl; reflexivity |
        idtac
      ]).
      (* For i >= 22, both lists return None *)
      simpl. reflexivity.
    + split.
      * simpl.
        (* Tactic to prove Permutation for concrete lists by removing common elements *)
        Ltac solve_perm :=
          match goal with
          | [ |- Permutation [] [] ] => apply Permutation_refl
          | [ |- Permutation (?x :: ?xs) ?ys ] =>
              eapply Permutation_trans; [
                apply Permutation_cons; [ reflexivity | solve_perm ] |
                apply Permutation_sym; apply Permutation_Add; 
                repeat first [ apply Add_head | apply Add_cons ]
              ]
          end.
        solve_perm.
      * simpl.
        (* Prove Sortedness *)
        repeat (apply Sorted_cons; [| apply HdRel_cons; [ lia | ] || apply HdRel_nil ]).
        apply Sorted_nil.
Qed.