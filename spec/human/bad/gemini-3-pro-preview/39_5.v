Require Import Coq.Init.Nat.
Require Import Coq.Arith.Arith.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Coq.Lists.ListSet.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition IsPrime (n : nat) : Prop :=
  1 < n /\ (forall d : nat, n mod d = 0 -> d = 1 \/ d = n).

(* fib i returns the i-th Fibonacci number *)
Fixpoint fib (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => match n' with
            | 0 => 1
            | S n'' => fib n' + fib n''
            end
  end.

Definition IsFib (n : nat) : Prop := exists i : nat, fib i = n.

Definition IsPrimeFib (n : nat) : Prop :=
  IsPrime n /\ IsFib n.

Definition problem_39_pre (n : nat) : Prop := (n >= 1)%nat.

Definition problem_39_spec (n r : nat) : Prop :=
  IsPrimeFib r /\
  (exists (S : list nat),
    length S = n - 1 /\
    NoDup S /\
    (forall y : nat, In y S <-> (y < r /\ IsPrimeFib y))
  ).

(* Helper definitions for the proof *)

Fixpoint check_divs (n k : nat) : bool :=
  match k with
  | 0 => true
  | 1 => true
  | S k' => if n mod (S k') =? 0 then false else check_divs n k'
  end.

Lemma check_divs_correct : forall n k,
  check_divs n k = true ->
  forall d, 1 < d <= k -> n mod d <> 0.
Proof.
  induction k.
  - intros; lia.
  - intros H d Hd.
    simpl in H.
    destruct k.
    + lia.
    + destruct (n mod (S (S k)) =? 0) eqn:Heq.
      * discriminate.
      * apply Nat.eqb_neq in Heq.
        apply IHk in H.
        destruct (Nat.eq_dec d (S (S k))).
        { subst. assumption. }
        { apply H. lia. }
Qed.

Lemma prime_check_ok : forall n,
  1 < n ->
  check_divs n (n - 1) = true ->
  IsPrime n.
Proof.
  intros n Hlt Hcheck.
  split; auto.
  intros d Hdiv.
  destruct (le_gt_dec d 1).
  { destruct d; [ simpl in Hdiv; discriminate | left; lia ]. }
  destruct (le_gt_dec d (n - 1)).
  {
    apply check_divs_correct with (d := d) in Hcheck; auto.
    rewrite Hdiv in Hcheck. destruct Hcheck. reflexivity.
  }
  {
    right.
    assert (d = n \/ d > n) by lia.
    destruct H0; auto.
    apply Nat.mod_small in H0.
    rewrite H0 in Hdiv.
    discriminate.
  }
Qed.

Lemma fib_mono : forall n, fib n <= fib (S n).
Proof.
  intro n.
  destruct n.
  - simpl. lia.
  - destruct n.
    + simpl. lia.
    + simpl. lia.
Qed.

Lemma fib_mono_general : forall n m, n <= m -> fib n <= fib m.
Proof.
  intros n m H.
  induction H.
  - reflexivity.
  - apply Nat.le_trans with (fib m); auto.
    apply fib_mono.
Qed.

Example problem_39_test_case : problem_39_spec 5 89.
Proof.
  unfold problem_39_spec.
  split.
  - (* IsPrimeFib 89 *)
    unfold IsPrimeFib. split.
    + apply prime_check_ok.
      * lia.
      * vm_compute. reflexivity.
    + exists 11. vm_compute. reflexivity.
  
  - (* Set property *)
    exists [2; 3; 5; 13].
    split.
    + simpl. reflexivity.
    + split.
      * repeat constructor; intro H; inversion H; try inversion H0; try inversion H1; try inversion H2.
      * intros y. split.
        { (* In -> ... *)
          intro Hin.
          repeat destruct Hin as [Heq | Hin]; try subst y.
          - split; [ lia | ].
            unfold IsPrimeFib. split.
            + apply prime_check_ok; [ lia | vm_compute; reflexivity ].
            + exists 3. simpl. reflexivity.
          - split; [ lia | ].
            unfold IsPrimeFib. split.
            + apply prime_check_ok; [ lia | vm_compute; reflexivity ].
            + exists 4. simpl. reflexivity.
          - split; [ lia | ].
            unfold IsPrimeFib. split.
            + apply prime_check_ok; [ lia | vm_compute; reflexivity ].
            + exists 5. simpl. reflexivity.
          - split; [ lia | ].
            unfold IsPrimeFib. split.
            + apply prime_check_ok; [ lia | vm_compute; reflexivity ].
            + exists 7. simpl. reflexivity.
          - inversion Hin.
        }
        { (* ... -> In *)
          intros [Hlt [Hp Hf]].
          destruct Hf as [i Hfib].
          assert (Hi: i <= 10).
          {
            destruct (le_lt_dec 11 i).
            - apply fib_mono_general in l.
              rewrite Hfib in l.
              assert (fib 11 = 89) by (vm_compute; reflexivity).
              rewrite H in l.
              lia.
            - lia.
          }
          (* Enumeration of i *)
          assert (Hcases: i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10) by lia.
          destruct Hcases as [? | [? | [? | [? | [? | [? | [? | [? | [? | [? | ?]]]]]]]]]].
          + (* 0 *) subst. simpl in Hfib. subst y. destruct Hp as [Hgt _]. lia.
          + (* 1 *) subst. simpl in Hfib. subst y. destruct Hp as [Hgt _]. lia.
          + (* 2 *) subst. simpl in Hfib. subst y. destruct Hp as [Hgt _]. lia.
          + (* 3 -> 2 *) subst. simpl in Hfib. subst y. left. reflexivity.
          + (* 4 -> 3 *) subst. simpl in Hfib. subst y. right; left. reflexivity.
          + (* 5 -> 5 *) subst. simpl in Hfib. subst y. right; right; left. reflexivity.
          + (* 6 -> 8 *) subst. simpl in Hfib. subst y.
            destruct Hp as [_ Hchk]. specialize (Hchk 2).
            assert (8 mod 2 = 0) by reflexivity.
            apply Hchk in H. destruct H; discriminate.
          + (* 7 -> 13 *) subst. simpl in Hfib. subst y. right; right; right; left. reflexivity.
          + (* 8 -> 21 *) subst. simpl in Hfib. subst y.
            destruct Hp as [_ Hchk]. specialize (Hchk 3).
            assert (21 mod 3 = 0) by reflexivity.
            apply Hchk in H. destruct H; discriminate.
          + (* 9 -> 34 *) subst. simpl in Hfib. subst y.
            destruct Hp as [_ Hchk]. specialize (Hchk 2).
            assert (34 mod 2 = 0) by reflexivity.
            apply Hchk in H. destruct H; discriminate.
          + (* 10 -> 55 *) subst. simpl in Hfib. subst y.
            destruct Hp as [_ Hchk]. specialize (Hchk 5).
            assert (55 mod 5 = 0) by reflexivity.
            apply Hchk in H. destruct H; discriminate.
        }
Qed.