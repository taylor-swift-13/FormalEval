Require Import List.
Require Import ZArith.
Require Import Lia.
Import ListNotations.

(* Specification definitions *)
Definition coord := (nat * nat)%type.

Fixpoint find_in_row_desc (row : list Z) (x : Z) (row_idx : nat) (col_idx : nat) : list coord :=
  match row with
  | [] => []
  | h :: t =>
    let rest := find_in_row_desc t x row_idx (S col_idx) in
    if Z.eqb h x then rest ++ [(row_idx, col_idx)] else rest
  end.

Fixpoint get_row_helper (lst : list (list Z)) (x : Z) (row_idx : nat) : list coord :=
  match lst with
  | [] => []
  | row :: rest =>
    find_in_row_desc row x row_idx 0 ++ get_row_helper rest x (S row_idx)
  end.

Definition get_row_spec (lst : list (list Z)) (x : Z) (result : list coord) : Prop :=
  result = get_row_helper lst x 0 /\
  (forall p, In p result -> 
    exists row, nth_error lst (fst p) = Some row /\ 
                nth_error row (snd p) = Some x) /\
  (forall i j, 
    match nth_error lst i with
    | Some row => 
      match nth_error row j with
      | Some v => v = x -> In (i, j) result
      | None => True
      end
    | None => True
    end) /\
  (forall i1 j1 i2 j2 idx1 idx2,
    nth_error result idx1 = Some (i1, j1) ->
    nth_error result idx2 = Some (i2, j2) ->
    idx1 < idx2 ->
    (i1 < i2 \/ (i1 = i2 /\ j1 > j2))).

(* Test case *)
Definition input_data : list (list Z) := 
  [[1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 6%Z]; 
   [1%Z; 2%Z; 3%Z; 4%Z; 1%Z; 6%Z]; 
   [1%Z; 2%Z; 3%Z; 4%Z; 5%Z; 1%Z]].

Definition target_val : Z := 1%Z.

Definition output_data : list coord := 
  [(0, 0); (1, 4); (1, 0); (2, 5); (2, 0)].

Example test_case_proof : get_row_spec input_data target_val output_data.
Proof.
  unfold get_row_spec.
  repeat split.
  
  (* 1. Functional Correctness *)
  - vm_compute. reflexivity.

  (* 2. Soundness *)
  - intros p H.
    simpl in H.
    (* Use subst instead of rewrite to avoid 'Cannot find a relation to rewrite' error *)
    destruct H as [H | [H | [H | [H | [H | H]]]]]; subst p; simpl.
    + exists [1; 2; 3; 4; 5; 6]%Z. split; reflexivity.
    + exists [1; 2; 3; 4; 1; 6]%Z. split; reflexivity.
    + exists [1; 2; 3; 4; 1; 6]%Z. split; reflexivity.
    + exists [1; 2; 3; 4; 5; 1]%Z. split; reflexivity.
    + exists [1; 2; 3; 4; 5; 1]%Z. split; reflexivity.
    + contradiction.

  (* 3. Completeness *)
  - intros i j.
    simpl.
    destruct i as [| i].
    + (* Row 0 *)
      destruct j as [| j]; [intros _; left; reflexivity |].
      destruct j as [| j]; [intros H; inversion H |].
      destruct j as [| j]; [intros H; inversion H |].
      destruct j as [| j]; [intros H; inversion H |].
      destruct j as [| j]; [intros H; inversion H |].
      destruct j as [| j]; [intros H; inversion H |].
      trivial.
    + destruct i as [| i].
      * (* Row 1 *)
        destruct j as [| j]; [intros _; right; right; left; reflexivity |].
        destruct j as [| j]; [intros H; inversion H |].
        destruct j as [| j]; [intros H; inversion H |].
        destruct j as [| j]; [intros H; inversion H |].
        destruct j as [| j]; [intros _; right; left; reflexivity |].
        destruct j as [| j]; [intros H; inversion H |].
        trivial.
      * destruct i as [| i].
        -- (* Row 2 *)
           destruct j as [| j]; [intros _; do 4 right; left; reflexivity |].
           destruct j as [| j]; [intros H; inversion H |].
           destruct j as [| j]; [intros H; inversion H |].
           destruct j as [| j]; [intros H; inversion H |].
           destruct j as [| j]; [intros H; inversion H |].
           destruct j as [| j]; [intros _; do 3 right; left; reflexivity |].
           trivial.
        -- (* Row > 2 *)
           trivial.

  (* 4. Ordering *)
  - intros i1 j1 i2 j2 idx1 idx2 H1 H2 Hlt.
    destruct idx1; simpl in H1.
    + (* idx1 = 0 *)
      inversion H1; subst.
      destruct idx2; simpl in H2; try lia.
      * inversion H2; subst. left; lia.
      * destruct idx2; simpl in H2; try lia.
        { inversion H2; subst. left; lia. }
        destruct idx2; simpl in H2; try lia.
        { inversion H2; subst. left; lia. }
        destruct idx2; simpl in H2; try lia.
        { inversion H2; subst. left; lia. }
        discriminate.
    + destruct idx1; simpl in H1.
      * (* idx1 = 1 *)
        inversion H1; subst.
        destruct idx2; simpl in H2; try lia.
        destruct idx2; simpl in H2; try lia.
        { inversion H2; subst. right. split; auto. lia. }
        destruct idx2; simpl in H2; try lia.
        { inversion H2; subst. left; lia. }
        destruct idx2; simpl in H2; try lia.
        { inversion H2; subst. left; lia. }
        discriminate.
      * destruct idx1; simpl in H1.
        -- (* idx1 = 2 *)
           inversion H1; subst.
           destruct idx2; simpl in H2; try lia.
           destruct idx2; simpl in H2; try lia.
           destruct idx2; simpl in H2; try lia.
           { inversion H2; subst. left; lia. }
           destruct idx2; simpl in H2; try lia.
           { inversion H2; subst. left; lia. }
           discriminate.
        -- destruct idx1; simpl in H1.
           ++ (* idx1 = 3 *)
              inversion H1; subst.
              destruct idx2; simpl in H2; try lia.
              destruct idx2; simpl in H2; try lia.
              destruct idx2; simpl in H2; try lia.
              destruct idx2; simpl in H2; try lia.
              { inversion H2; subst. right. split; auto. lia. }
              discriminate.
           ++ destruct idx1; simpl in H1.
              ** (* idx1 = 4 *)
                 inversion H1; subst.
                 destruct idx2; simpl in H2; try lia.
                 do 4 (destruct idx2; simpl in H2; try lia).
                 discriminate.
              ** discriminate.
Qed.