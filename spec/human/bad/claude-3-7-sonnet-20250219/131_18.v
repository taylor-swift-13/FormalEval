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

Example test_case_952 :
  problem_131_spec 952 45.
Proof.
  unfold problem_131_spec, digits_impl.
  unfold get_digits.
  unfold get_digits_helper.
  simpl.
  (* get_digits_helper 952 952 unfolds as:
     952 mod 10 = 2 :: get_digits_helper (952 / 10 = 95) 951
     95 mod 10 = 5 :: get_digits_helper (95 / 10 = 9) 950
     9 mod 10 = 9 :: get_digits_helper (9 / 10 = 0) 949
     get_digits_helper 0 949 = []
     so get_digits 952 = [2;5;9]
  *)
  (* filter Nat.odd [2;5;9] = [5;9] *)
  (* product [5;9] = 45 *)
  reflexivity.
Qed.