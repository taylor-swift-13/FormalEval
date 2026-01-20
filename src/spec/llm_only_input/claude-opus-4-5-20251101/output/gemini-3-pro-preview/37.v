Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Arith.Arith.
Require Import Lia.

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

Example test_sort_even : sort_even_spec [1%Z; 2%Z; 3%Z] [1%Z; 2%Z; 3%Z].
Proof.
  unfold sort_even_spec.
  split.
  - (* length l = length res *)
    simpl. reflexivity.
  - split.
    + (* odd indices preserved *)
      intros i Hi Hodd.
      simpl in Hi.
      destruct i as [|[|[|i']]].
      * (* i = 0 *) simpl in Hodd. discriminate.
      * (* i = 1 *) simpl. reflexivity.
      * (* i = 2 *) simpl in Hodd. discriminate.
      * (* i >= 3 *) lia.
    + split.
      * (* Permutation of evens *)
        simpl. apply Permutation_refl.
      * (* Sorted evens *)
        simpl.
        apply Sorted_cons.
        -- apply Sorted_cons.
           ++ apply Sorted_nil.
           ++ apply HdRel_nil.
        -- apply HdRel_cons. lia.
Qed.