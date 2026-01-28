Require Import Coq.Lists.List Coq.Arith.Arith Coq.micromega.Lia.
Import ListNotations.

Fixpoint get_digits_helper (n fuel : nat) : list nat :=
  match fuel with
  | 0 => []
  | S f' =>
    match n with
    | 0 => []
    | _ => (n mod 10) :: get_digits_helper (n / 10) f'
    end
  end.

Definition get_digits (n : nat) : list nat :=
  get_digits_helper n n.

Fixpoint product (l : list nat) : nat :=
  match l with
  | [] => 1
  | h :: t => h * product t
  end.

Definition digits_impl (n : nat) : nat :=
  let ds := filter Nat.odd (get_digits n) in
  match ds with
  | [] => 0
  | _ => product ds
  end.

Definition problem_131_pre (n : nat) : Prop := n > 0.

Definition problem_131_spec (n : nat) (output : nat) : Prop :=
  output = digits_impl n.

Example test_case_98765 :
  problem_131_spec 98765 315.
Proof.
  unfold problem_131_spec, digits_impl, get_digits.
  revert 98765.
  (* Compute get_digits_helper 98765 98765 without unfolding all *)
  (* Instead, manually reduce with nat operations stepwise *)
  (* get_digits_helper 98765 98765: 98765 mod 10 = 5 *)
  (* get_digits_helper (98765 / 10=9876) 98764 *)
  (* Continue extracting digits: 5 :: 6 :: 7 :: 8 :: 9 *)
  (* The digits list is [5;6;7;8;9] *)
  remember (filter Nat.odd [5;6;7;8;9]) as odd_digits eqn:Heqodd.
  simpl in Heqodd.
  unfold filter in Heqodd.
  simpl in Heqodd.
  (* filter Nat.odd [5;6;7;8;9] = 5 :: filter Nat.odd [6;7;8;9] *)
  (* 6 is even, 7 is odd, 8 even, 9 odd *)
  (* So odd digits are [5;7;9] *)
  assert (odd_digits = [5;7;9]).
  { subst odd_digits.
    simpl.
    reflexivity.
  }
  subst odd_digits.
  simpl.
  reflexivity.
Qed.