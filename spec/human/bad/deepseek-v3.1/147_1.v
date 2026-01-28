Require Import ZArith.
Require Import List.
Require Import Arith.
Require Import Psatz.
Import ListNotations.
Open Scope Z_scope.

(* Definition from specification *)
Definition a_val (i : nat) : Z :=
  let i_z := Z.of_nat i in
  i_z * i_z - i_z + 1.

Definition is_valid_triple (n i j k : nat) : Prop :=
  (1 <= i)%nat /\ (i < j)%nat /\ (j < k)%nat /\ (k <= n)%nat /\
  (a_val i + a_val j + a_val k) mod 3 = 0.

Definition problem_147_pre (n : nat) : Prop := n > 0.

Definition problem_147_spec (n : nat) (output : nat) : Prop :=
  exists (l : list (nat * nat * nat)),
    (forall ijk, In ijk l ->
      let '(i, j, k) := ijk in is_valid_triple n i j k) /\
    (forall i j k, is_valid_triple n i j k -> In (i, j, k) l) /\
    NoDup l /\
    output = length l.

(* Helper lemma: compute a_val results *)
Lemma a_val_compute : forall i, a_val i = (Z.of_nat i) * (Z.of_nat i) - (Z.of_nat i) + 1.
Proof.
  intros i. unfold a_val. reflexivity.
Qed.

(* Compute specific a_val values *)
Lemma a_val_1 : a_val 1 = 1.
Proof. compute. reflexivity. Qed.

Lemma a_val_2 : a_val 2 = 3.
Proof. compute. reflexivity. Qed.

Lemma a_val_3 : a_val 3 = 7.
Proof. compute. reflexivity. Qed.

Lemma a_val_4 : a_val 4 = 13.
Proof. compute. reflexivity. Qed.

Lemma a_val_5 : a_val 5 = 21.
Proof. compute. reflexivity. Qed.

(* Test case proof for n = 5 *)
Example test_case_n5 : problem_147_spec 5 1.
Proof.
  unfold problem_147_spec.
  (* The only valid triple is (1, 3, 4) which corresponds to values (1, 7, 13) *)
  exists [(1, 3, 4)].
  repeat split.
  - (* All elements in list are valid triples *)
    intros ijk H.
    simpl in H.
    destruct H as [H|H].
    + injection H as H1 H2 H3.
      rewrite H1, H2, H3.
      unfold is_valid_triple.
      repeat split; try lia.
      rewrite a_val_1, a_val_3, a_val_4.
      compute. reflexivity.
    + contradiction.
  - (* All valid triples are in the list *)
    intros i j k H.
    unfold is_valid_triple in H.
    destruct H as [H1 [H2 [H3 [H4 H5]]]].
    
    (* Generate all possible triples with 1 <= i < j < k <= 5 *)
    (* We'll enumerate them explicitly since n is small *)
    assert (all_triples : list (nat * nat * nat) :=
      [(1, 2, 3); (1, 2, 4); (1, 2, 5);
       (1, 3, 4); (1, 3, 5); (1, 4, 5);
       (2, 3, 4); (2, 3, 5); (2, 4, 5);
       (3, 4, 5)]).
    
    (* Check which triple satisfies the mod condition *)
    simpl.
    (* Only need to show that (i, j, k) must be (1, 3, 4) *)
    assert (i_le_3 : (i <= 3)%nat) by lia.
    assert (j_le_4 : (j <= 4)%nat) by lia.
    assert (k_le_5 : (k <= 5)%nat) by lia.
    
    (* Case analysis on possible values *)
    destruct (le_lt_dec 1 i) as [Hi1|Hi1]; try lia.
    destruct (le_lt_dec i 3) as [Hi2|Hi2]; try lia.
    destruct (le_lt_dec (S i) j) as [Hj1|Hj1]; try lia.
    destruct (le_lt_dec j 4) as [Hj2|Hj2]; try lia.
    destruct (le_lt_dec (S j) k) as [Hk1|Hk1]; try lia.
    destruct (le_lt_dec k 5) as [Hk2|Hk2]; try lia.
    
    (* Now we have specific ranges, check each case *)
    destruct i as [|i]; try lia.
    destruct i as [|i]; try lia.  (* i = 1 *)
    destruct i as [|i]; try lia.  (* i = 2 *)
    destruct i as [|i]; try lia.  (* i = 3 *)
    
    - (* Case i = 1 *)
      destruct j as [|j]; try lia.
      destruct j as [|j]; try lia.  (* j = 2 *)
      destruct j as [|j]; try lia.  (* j = 3 *)
      destruct j as [|j]; try lia.  (* j = 4 *)
      + (* j = 2 *)
        destruct k as [|k]; try lia.
        destruct k as [|k]; try lia.  (* k = 3 *)
        destruct k as [|k]; try lia.  (* k = 4 *)
        destruct k as [|k]; try lia.  (* k = 5 *)
        * (* k = 3: check mod *)
          rewrite a_val_1, a_val_2, a_val_3 in H5.
          compute in H5. discriminate H5.
        * (* k = 4: check mod *)
          rewrite a_val_1, a_val_2, a_val_4 in H5.
          compute in H5. discriminate H5.
        * (* k = 5: check mod *)
          rewrite a_val_1, a_val_2, a_val_5 in H5.
          compute in H5. discriminate H5.
      + (* j = 3 *)
        destruct k as [|k]; try lia.
        destruct k as [|k]; try lia.  (* k = 4 *)
        destruct k as [|k]; try lia.  (* k = 5 *)
        * (* k = 4: valid case *)
          left. reflexivity.
        * (* k = 5: check mod *)
          rewrite a_val_1, a_val_3, a_val_5 in H5.
          compute in H5. discriminate H5.
      + (* j = 4 *)
        destruct k as [|k]; try lia.
        destruct k as [|k]; try lia.  (* k = 5 *)
        rewrite a_val_1, a_val_4, a_val_5 in H5.
        compute in H5. discriminate H5.
    
    - (* Case i = 2 *)
      destruct j as [|j]; try lia.
      destruct j as [|j]; try lia.  (* j = 3 *)
      destruct j as [|j]; try lia.  (* j = 4 *)
      + (* j = 3 *)
        destruct k as [|k]; try lia.
        destruct k as [|k]; try lia.  (* k = 4 *)
        destruct k as [|k]; try lia.  (* k = 5 *)
        * (* k = 4: check mod *)
          rewrite a_val_2, a_val_3, a_val_4 in H5.
          compute in H5. discriminate H5.
        * (* k = 5: check mod *)
          rewrite a_val_2, a_val_3, a_val_5 in H5.
          compute in H5. discriminate H5.
      + (* j = 4 *)
        destruct k as [|k]; try lia.
        destruct k as [|k]; try lia.  (* k = 5 *)
        rewrite a_val_2, a_val_4, a_val_5 in H5.
        compute in H5. discriminate H5.
    
    - (* Case i = 3 *)
      destruct j as [|j]; try lia.
      destruct j as [|j]; try lia.  (* j = 4 *)
      destruct k as [|k]; try lia.
      destruct k as [|k]; try lia.  (* k = 5 *)
      rewrite a_val_3, a_val_4, a_val_5 in H5.
      compute in H5. discriminate H5.
  
  - (* NoDup *)
    simpl. constructor; [constructor|]. constructor.
  - (* Length is 1 *)
    reflexivity.
Qed.