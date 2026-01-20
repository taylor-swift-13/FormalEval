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
  [300%Z; 500%Z; 6%Z; 7%Z; 290%Z; 8%Z; 289%Z; 20%Z; 104%Z; -277%Z; 8%Z; 104%Z; 200%Z; -8%Z; 700%Z; 900%Z; -901%Z; -200%Z; 800%Z; 1000%Z; 290%Z; -8%Z; 104%Z; 1000%Z]
  [-277%Z; 500%Z; 6%Z; -8%Z; 290%Z; 8%Z; 7%Z; 20%Z; 104%Z; 200%Z; 8%Z; 104%Z; 289%Z; -8%Z; 700%Z; 300%Z; -901%Z; -200%Z; 800%Z; 1000%Z; 290%Z; 900%Z; 104%Z; 1000%Z].
Proof.
  unfold sort_third_spec.
  split.
  - (* length *)
    simpl. reflexivity.
  - split.
    + (* indices preservation *)
      intros i H.
      (* Check indices 0 to 23 *)
      do 24 (destruct i; [ simpl in H; try discriminate; simpl; reflexivity | ]).
      (* Check indices >= 24 *)
      simpl. reflexivity.
    + split.
      * (* Permutation *)
        vm_compute.
        apply NoDup_Permutation.
        -- (* NoDup LHS *)
           repeat (constructor; [ intro Hin; simpl in Hin; repeat (destruct Hin as [Heq | Hin]; [ discriminate Heq | ]); contradiction | ]).
           apply NoDup_nil.
        -- (* NoDup RHS *)
           repeat (constructor; [ intro Hin; simpl in Hin; repeat (destruct Hin as [Heq | Hin]; [ discriminate Heq | ]); contradiction | ]).
           apply NoDup_nil.
        -- (* Inclusion *)
           intros x. split; intro Hx;
           repeat (destruct Hx as [Hx | Hx]; [ rewrite <- Hx; simpl; tauto | ]); try contradiction.
      * (* Sorted *)
        vm_compute.
        repeat constructor.
Qed.