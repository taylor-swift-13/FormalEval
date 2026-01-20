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

(* Helper tactics for the proof to handle large concrete lists efficiently *)

(* Tactic to solve Add predicate for concrete lists *)
Ltac prove_add :=
  first [ apply Add_head
        | apply Add_cons; prove_add ].

(* Tactic to solve Permutation for concrete lists by peeling off elements *)
Ltac solve_perm :=
  match goal with
  | |- Permutation [] [] => apply Permutation_nil
  | |- Permutation (?x :: ?xs) ?l =>
      apply Permutation_Add; [ prove_add | solve_perm ]
  end.

(* Tactic to solve Sorted for concrete Z lists *)
Ltac solve_sorted :=
  repeat (apply Sorted_cons; [| apply HdRel_cons; apply Z.leb_le; vm_compute; reflexivity ]);
  try apply Sorted_nil;
  try apply HdRel_nil.

Example test_case : sort_third_spec 
  [300; 500; 6; 7; 8; 289; 20; -105; -277; 104; 8; 7; 3; 12; 4; 5; 700; -5; -200; -901; 800; 1000]
  [-200; 500; 6; 3; 8; 289; 5; -105; -277; 7; 8; 7; 20; 12; 4; 104; 700; -5; 300; -901; 800; 1000].
Proof.
  unfold sort_third_spec.
  split.
  - (* 1. length res = length l *)
    vm_compute. reflexivity.
  - split.
    + (* 2. Preservation of indices not divisible by 3 *)
      intros i H.
      (* Since the lists are concrete and finite (length 22), we destruct i 22 times 
         to check the property for each index. *)
      do 22 (destruct i as [|i]; [
        (* For each concrete index, check the condition H *)
        vm_compute in H; 
        try congruence; (* If H reduces to False (0 <> 0), solve it *)
        vm_compute; reflexivity (* If H holds, check equality of nth_error *)
      | ]).
      (* For i >= 22, both nth_error are None *)
      vm_compute. reflexivity.
    + split.
      * (* 3. Permutation of extracted thirds *)
        (* Simplify the extraction first *)
        vm_compute.
        (* Prove permutation of the resulting concrete lists *)
        solve_perm.
      * (* 4. Sortedness of extracted thirds *)
        vm_compute.
        solve_sorted.
Qed.