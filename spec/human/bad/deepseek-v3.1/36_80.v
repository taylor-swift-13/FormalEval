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

Example test_case_2000 : problem_36_spec 2000 95.
Proof.
  unfold problem_36_spec, fizz_buzz_impl.
  simpl.
  repeat (try rewrite List.fold_left_app; try rewrite List.fold_left_seq).
  unfold List.seq.
  remember (List.seq 0 2000) as L.
  assert (H: length L = 2000) by (subst; apply List.length_seq).
  clear HeqL.
  unfold count_digit_7 in *.
  (* Computing manually or via a tactic *)
  (* Instead of fully unfolding, we can leverage simplification and brute-force sum *)
  reflexivity.
Qed.