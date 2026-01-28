Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.micromega.Lia.

Fixpoint evens_list (l : list Z) : list Z :=
  match l with
  | [] => []
  | x :: [] => [x]
  | x :: _ :: t => x :: evens_list t
  end.

Definition sort_even_spec (l : list Z) (l' : list Z) : Prop :=
  exists es,
    Sorted Z.le es /\
    Permutation es (evens_list l) /\
    length l' = length l /\
    forall i, i < length l ->
      (if Nat.even i
       then nth i l' 0%Z = nth (Nat.div2 i) es 0%Z
       else nth i l' 0%Z = nth i l 0%Z).

Example test_sort_even : sort_even_spec [1%Z; 2%Z; 3%Z] [1%Z; 2%Z; 3%Z].
Proof.
  unfold sort_even_spec.
  exists [1%Z; 3%Z].
  repeat split.
  - (* Sorted Z.le [1; 3] *)
    apply Sorted_cons.
    + apply Sorted_cons.
      * apply Sorted_nil.
      * apply HdRel_nil.
    + apply HdRel_cons.
      simpl. lia.
  - (* Permutation *)
    simpl. apply Permutation_refl.
  - (* Length *)
    simpl. reflexivity.
  - (* Indices *)
    intros i Hi.
    destruct i as [|i].
    + (* i = 0 *)
      vm_compute. reflexivity.
    + destruct i as [|i].
      * (* i = 1 *)
        vm_compute. reflexivity.
      * destruct i as [|i].
        -- (* i = 2 *)
           vm_compute. reflexivity.
        -- (* i >= 3 *)
           simpl in Hi. lia.
Qed.