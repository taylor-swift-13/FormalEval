Require Import Coq.Lists.List Coq.Arith.Arith Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_digits_helper (n : Z) (fuel : nat) : list Z :=
  match fuel with
  | 0%nat => []
  | S f' =>
    if Z.eqb n 0 then []
    else (n mod 10) :: get_digits_helper (n / 10) f'
  end.

Definition get_digits (n : Z) : list Z :=
  let fuel := Z.to_nat (Z.log2 n + 2) in
  get_digits_helper n fuel.

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

Definition problem_131_pre (n : Z) : Prop := n > 0.

Definition problem_131_spec (n : Z) (output : Z) : Prop :=
  output = digits_impl n.

Example test_case : problem_131_spec 182937457814614279640075438629345987263878749129823578184719333882443 2374385525072174368125.
Proof.
  unfold problem_131_spec.
  vm_compute.
  reflexivity.
Qed.