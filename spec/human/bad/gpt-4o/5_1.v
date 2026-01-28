Require Import List.
Require Import ZArith.
Require Import Arith.
Require Import Nat.
Require Import Lia.
Require Import Coq.Arith.PeanoNat.

Import ListNotations.

(* Specification definitions *)
Definition problem_5_pre (input output : list Z) : Prop := True.

Definition problem_5_spec (input output : list Z) (d : Z) : Prop :=
  (input = [] -> output = []) /\
  (forall n : nat,
      length input = n -> 1 <= n ->
      length output = 2 * n - 1 /\
      forall i : nat, i < 2 * n - 1 ->
        (Nat.Even i -> nth_error output i = nth_error input (i / 2)) /\
        (Nat.Odd i -> nth_error output i = Some d)
  ).

(* The actual 'intersperse' function *)
Fixpoint intersperse (l : list Z) (d : Z) : list Z :=
  match l with
  | [] => []
  | [x] => [x]
  | x :: xs => x :: d :: intersperse xs d
  end.

(* Helper lemma for intersperse function correctness *)
Lemma intersperse_length :
  forall (l : list Z) (d : Z),
    length l > 0 -> length (intersperse l d) = 2 * length l - 1.
Proof.
  intros l d H.
  induction l as [| x xs IH].
  - lia.
  - simpl in *. destruct xs.
    + simpl. lia.
    + simpl. specialize (IH d).
      assert (length (x :: z :: xs) > 0). { simpl. lia. }
      specialize (IH H0). simpl in IH.
      rewrite IH. lia.
Qed.

Lemma intersperse_correct :
  forall (l : list Z) (d : Z),
    length l > 0 ->
    forall i : nat, i < 2 * length l - 1 ->
      (Nat.Even i -> nth_error (intersperse l d) i = nth_error l (i / 2)) /\
      (Nat.Odd i -> nth_error (intersperse l d) i = Some d).
Proof.
  intros l d Hlen i Hi.
  generalize dependent i.
  induction l as [| x xs IH] using rev_ind.
  - simpl in Hlen. lia.
  - assert (Hxs: length (x :: xs) > 0) by simpl; lia.
    specialize (IH Hxs).
    intros i Hi.
    destruct (le_lt_dec (length xs) i).
    + unfold intersperse.
      rewrite app_length in Hi.
      simpl in Hi.
      apply Nat.lt_le_incl in Hi.
      rewrite Nat.add_sub_assoc in Hi.
      rewrite Nat.add_sub, Nat.mul_succ_r in Hi.
      rewrite Nat.add_succ_r in Hi.
      simpl in Hi.
      lia.
    + unfold intersperse.
      remember (intersperse xs d) as interspersed_xs.
      simpl.
      rewrite <- Heqinterspersed_xs.
      simpl.
      destruct i.
      * split; intros _.
        -- simpl. reflexivity.
        -- exfalso. apply Nat.Even_Odd_False. auto.
      * destruct i.
        -- split; intros.
           ++ exfalso. apply Nat.Even_Odd_False. auto.
           ++ simpl. reflexivity.
        -- simpl. destruct (Nat.even_spec i) as [Heven | Hodd].
           ++ rewrite Nat.div2_succ_double, Nat.div2_double.
              replace (S (S i) / 2) with ((S i / 2) + 1) by lia.
              replace (i / 2) with (Nat.div2 i) by lia.
              specialize (IH (S i / 2)).
              rewrite <- Heqinterspersed_xs in IH.
              destruct IH as [HevenIH _]. simpl in HevenIH.
              rewrite HevenIH; try lia.
              split; intros _; simpl; try reflexivity.
              apply lt_n_S, div2_decr_pos, PeanoNat.Nat.lt_pos_0.
              lia.
           ++ replace (S (S i) / 2) with (S (i / 2)) by lia.
              destruct IH as [_ HoddIH].
              rewrite <- Heqinterspersed_xs in HoddIH.
              rewrite HoddIH; try lia.
              split; intros; try reflexivity.
Qed.

(* Test case: *)
Example intersperse_test_case :
  problem_5_spec [] [] 7%Z.
Proof.
  unfold problem_5_spec.
  split.
  - reflexivity.
  - intros n Hlen Hn.
    simpl in Hlen.
    lia.
Qed.

Qed.