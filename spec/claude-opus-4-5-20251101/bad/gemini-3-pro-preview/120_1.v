Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
Import ListNotations.

Open Scope Z_scope.

(* Specification Definitions *)

Definition is_sorted (l : list Z) : Prop :=
  forall i j, (0 <= i < j)%nat -> (j < length l)%nat ->
    match nth_error l i, nth_error l j with
    | Some a, Some b => a <= b
    | _, _ => True
    end.

Definition count_occ_Z (l : list Z) (x : Z) : nat :=
  count_occ Z.eq_dec l x.

Definition is_permutation_of_sublist (result original : list Z) : Prop :=
  forall x, (count_occ_Z result x <= count_occ_Z original x)%nat.

Definition are_top_k_elements (result original : list Z) (k : nat) : Prop :=
  forall x y,
    In x result ->
    In y original ->
    ~In y result ->
    count_occ_Z result y = 0%nat ->
    x >= y.

Definition maximum_spec (arr : list Z) (k : nat) (result : list Z) : Prop :=
  length result = k /\
  is_sorted result /\
  is_permutation_of_sublist result arr /\
  (k <= length arr)%nat /\
  (forall x, In x result -> In x arr) /\
  (forall dropped, 
    In dropped arr -> 
    (count_occ_Z arr dropped > count_occ_Z result dropped)%nat ->
    forall kept, In kept result -> kept >= dropped).

(* Test Case Proof *)

Example test_case : maximum_spec [-3; -4; 5] 3 [-4; -3; 5].
Proof.
  unfold maximum_spec.
  repeat split.
  
  (* 1. length result = k *)
  - simpl. reflexivity.
  
  (* 2. is_sorted result *)
  - unfold is_sorted.
    intros i j H_lt H_len.
    (* Case analysis on indices for the list of length 3 *)
    destruct i as [|i].
    + (* i = 0 *)
      destruct j as [|j].
      * (* j = 0 *) lia.
      * destruct j as [|j].
        -- (* j = 1 *) simpl. lia. (* -4 <= -3 *)
        -- destruct j as [|j].
           ++ (* j = 2 *) simpl. lia. (* -4 <= 5 *)
           ++ (* j >= 3 *) simpl in H_len. lia.
    + (* i > 0 *)
      destruct i as [|i].
      * (* i = 1 *)
        destruct j as [|j].
        -- (* j = 0 *) lia.
        -- destruct j as [|j].
           ++ (* j = 1 *) lia.
           ++ destruct j as [|j].
              ** (* j = 2 *) simpl. lia. (* -3 <= 5 *)
              ** (* j >= 3 *) simpl in H_len. lia.
      * (* i >= 2 *)
        (* i < j -> j >= 3, which contradicts length = 3 *)
        simpl in H_len. lia.

  (* 3. is_permutation_of_sublist *)
  - unfold is_permutation_of_sublist, count_occ_Z.
    intro x. simpl.
    (* Check counts for all cases. The underscore lets Coq infer the value from the goal. *)
    repeat destruct (Z.eq_dec _ x); simpl; try lia.

  (* 4. k <= length arr *)
  - simpl. lia.

  (* 5. In x result -> In x arr *)
  - intros x H. simpl in H. 
    destruct H as [H | [H | [H | H]]]; subst; simpl; auto.

  (* 6. Dropped elements condition *)
  - intros dropped H_in H_count kept H_kept.
    unfold count_occ_Z in *. simpl in *.
    (* Prove contradiction in H_count (count arr > count result) *)
    repeat destruct (Z.eq_dec _ dropped); simpl in *; try lia.
Qed.