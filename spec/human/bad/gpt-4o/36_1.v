Require Import Coq.Lists.List Coq.Arith.Arith Coq.Arith.EqNat Coq.Bool.Bool.
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

Example test_fizz_buzz_50 : forall output,
  problem_36_spec 50 output -> output = 0.
Proof.
  intros output Hspec.
  unfold problem_36_spec, fizz_buzz_impl in Hspec.
  simpl in Hspec.
  assert (H: forall x, x < 50 -> (x mod 11 = 0 \/ x mod 13 = 0) -> count_digit_7 x = 0).
  { intros x Hlt Hdiv.
    (* We are checking the numbers divisible by 11 or 13 less than 50 *)
    (* They are: 0, 11, 13, 22, 26, 33, 39, 44 *)
    repeat (destruct x as [| x]; simpl; try reflexivity;
            match goal with
            | |- context [ Nat.eqb ?a ?b ] => destruct (Nat.eqb a b) eqn:Heq; auto
            end).
  }
  induction (List.seq 0 50) as [|a l' IH].
  - simpl in Hspec. subst. reflexivity.
  - simpl in Hspec.
    destruct (orb (Nat.eqb (a mod 11) 0) (Nat.eqb (a mod 13) 0)) eqn:Hor.
    + apply orb_true_iff in Hor; destruct Hor.
      * apply Nat.eqb_eq in H0.
        specialize (H a ltac:(apply in_seq in H0; lia) (or_introl H0)).
        rewrite H in Hspec. apply IH in Hspec. assumption.
      * apply Nat.eqb_eq in H0.
        specialize (H a ltac:(apply in_seq in H0; lia) (or_intror H0)).
        rewrite H in Hspec. apply IH in Hspec. assumption.
    + apply IH in Hspec. assumption.
Qed.