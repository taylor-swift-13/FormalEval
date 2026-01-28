Require Import Coq.Lists.List Coq.Arith.Arith Coq.Bool.Bool Coq.ZArith.ZArith.
Import ListNotations.

Fixpoint count_digit_7_aux (k fuel : nat) : nat :=
  match fuel with
  | 0 => 0
  | S f' =>
    match k with
    | 0 => 0
    | _ =>
      (if Nat.eqb (k mod 10) 7 then 1 else 0) +
      count_digit_7_aux (k / 10) f'
    end
  end.

Definition count_digit_7 (k : nat) : nat :=
  count_digit_7_aux k k.

Definition fizz_buzz_impl (n : nat) : nat :=
  List.fold_left
    (fun acc i =>
      acc +
      (if orb (Nat.eqb (i mod 11) 0) (Nat.eqb (i mod 13) 0) then
         count_digit_7 i
       else
         0))
    (List.seq 0 n)
    0.

Definition problem_36_pre (n : nat) : Prop := True.

Definition problem_36_spec (n : nat) (output : nat) : Prop :=
  output = fizz_buzz_impl n.

Example test_fizz_buzz_50:
  problem_36_spec 50 0.
Proof.
  unfold problem_36_spec, fizz_buzz_impl.
  (* We analyze the list seq 0 50 and sum over i *)
  (* We'll do induction on the list, carrying the accumulator *)
  remember (seq 0 50) as l eqn:Hl.
  generalize 0 as acc.
  induction l as [|hd tl IH]; intros acc.
  - simpl. intros. subst. reflexivity.
  - simpl.
    destruct (orb (Nat.eqb (hd mod 11) 0) (Nat.eqb (hd mod 13) 0)) eqn:Hdiv.
    + (* i divisible by 11 or 13 *)
      (* All such multiples less than 50: 0,11,13,22,26,33,39,44 *)
      assert (Hhd_in :
        hd = 0 \/ hd = 11 \/ hd = 13 \/ hd = 22 \/ hd = 26 \/ hd = 33 \/ hd = 39 \/ hd = 44).
      {
        apply orb_true_iff in Hdiv.
        destruct Hdiv as [H11 | H13].
        - apply Nat.eqb_eq in H11.
          apply Nat.mod_divides in H11; try lia.
          destruct H11 as [k Hk].
          subst hd.
          (* multiples of 11 < 50 are 0,11,22,33,44 *)
          assert (k <= 4) by lia.
          destruct k; simpl; lia.
        - apply Nat.eqb_eq in H13.
          apply Nat.mod_divides in H13; try lia.
          destruct H13 as [k Hk].
          subst hd.
          (* multiples of 13 <50 are 0,13,26,39 *)
          assert (k <= 3) by lia.
          destruct k; simpl; lia.
      }
      (* For all those hd, count_digit_7 hd = 0 *)
      assert (count_digit_7 hd = 0).
      {
        destruct Hhd_in as [->|[->|[->|[->|[->|[->|[->|->]]]]]]].
        all: unfold count_digit_7, count_digit_7_aux; simpl;
          try (repeat rewrite Nat.eqb_refl);
          try reflexivity;
          try lia.
      }
      rewrite H.
      apply IH.
    + (* i not divisible by 11 or 13 *)
      apply IH.
Qed.