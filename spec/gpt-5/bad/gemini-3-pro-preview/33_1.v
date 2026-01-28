Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.

Import ListNotations.

Definition third_indices (l : list Z) : list nat :=
  filter (fun i => Nat.eqb (Nat.modulo i 3) 0) (seq 0 (length l)).

Definition third_elems (l : list Z) : list Z :=
  map (fun i => nth i l 0%Z) (third_indices l).

Definition sort_third_spec (l : list Z) (l' : list Z) : Prop :=
  exists s',
    Sorted Z.le s' /\
    Permutation (third_elems l) s' /\
    length l' = length l /\
    (forall i, i < length l ->
      Nat.modulo i 3 <> 0 ->
      nth_error l' i = nth_error l i) /\
    (forall k, k < length (third_indices l) ->
      nth_error l' (nth k (third_indices l) 0) = nth_error s' k).

Example test_sort_third : sort_third_spec [1%Z; 2%Z; 3%Z] [1%Z; 2%Z; 3%Z].
Proof.
  unfold sort_third_spec.
  exists [1%Z].
  repeat split.
  - (* Sorted *)
    apply Sorted_cons.
    + apply Sorted_nil.
    + apply HdRel_nil.
  - (* Permutation *)
    unfold third_elems, third_indices.
    simpl. apply Permutation_refl.
  - (* Length *)
    simpl. reflexivity.
  - (* Preservation of non-third indices *)
    intros i Hi Hmod.
    destruct i as [| [| [| i'] ] ].
    + (* i = 0 *)
      simpl in Hmod. exfalso. apply Hmod. reflexivity.
    + (* i = 1 *)
      simpl. reflexivity.
    + (* i = 2 *)
      simpl. reflexivity.
    + (* i >= 3 *)
      simpl in Hi. lia.
  - (* Correct placement of sorted third elements *)
    intros k Hk.
    unfold third_indices in *. simpl in *.
    destruct k as [| k'].
    + (* k = 0 *)
      simpl. reflexivity.
    + (* k > 0 *)
      lia.
Qed.