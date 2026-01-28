Require Import Coq.Lists.List Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_digits_helper (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | 0%nat => []
  | S f' =>
    if n =? 0 then []
    else (n mod 10) :: get_digits_helper (n / 10) f'
  end.

Definition get_digits (n : Z) : list Z :=
  get_digits_helper n (Z.to_nat (Z.log2 n) + 16)%nat.

Fixpoint product (l : list Z) : Z :=
  match l with
  | [] => 1
  | h :: t => h * product t
  end.

Definition digits_impl (n : Z) : Z :=
  let ds := filter Z.odd (get_digits n) in
  match ds with
  | [] => 0
  | _ => product ds
  end.

(* n 为正整数 *)
Definition problem_131_pre (n : Z) : Prop := n > 0.

Definition problem_131_spec (n : Z) (output : Z) : Prop :=
  output = digits_impl n.

Example test_case : problem_131_spec 323456789101112131415161718192021222324252627282930313233343535 415266336646875.
Proof.
  unfold problem_131_spec.
  unfold digits_impl.
  unfold get_digits.
  vm_compute.
  reflexivity.
Qed.