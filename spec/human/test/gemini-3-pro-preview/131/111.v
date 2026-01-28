Require Import Coq.Lists.List Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_digits_helper (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | O => []
  | S f' =>
    if n =? 0 then []
    else (n mod 10) :: get_digits_helper (n / 10) f'
  end.

Definition get_digits (n : Z) : list Z :=
  get_digits_helper n (Z.to_nat (Z.log2 n) + 2)%nat.

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

Example test_case : problem_131_spec 3902482539585903843732859374089573948579380957409378540930757943758435987234095873947598343 149749111277833459456445972784093017578125.
Proof.
  unfold problem_131_spec, digits_impl, get_digits.
  vm_compute.
  reflexivity.
Qed.