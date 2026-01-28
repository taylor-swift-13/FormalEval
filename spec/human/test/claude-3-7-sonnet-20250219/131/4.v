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

Example test_case_5014 :
  problem_131_spec 5014 5.
Proof.
  unfold problem_131_spec, digits_impl.
  unfold get_digits.
  unfold get_digits_helper.
  simpl.
  (* get_digits_helper 5014 5014 unfolds as:  
     n=5014, fuel=5014: 5014 mod 10=4 :: get_digits_helper (5014/10=501) 5013
     n=501, fuel=5013: 501 mod 10=1 :: get_digits_helper (501/10=50) 5012
     n=50, fuel=5012: 50 mod 10=0 :: get_digits_helper (50/10=5) 5011
     n=5, fuel=5011: 5 mod 10=5 :: get_digits_helper (5/10=0) 5010
     n=0, fuel=5010: []
     so get_digits 5014 = [4; 1; 0; 5]
  *)
  (* filter Nat.odd [4;1;0;5] = [1;5] *)
  (* product [1;5] = 5 *)
  reflexivity.
Qed.