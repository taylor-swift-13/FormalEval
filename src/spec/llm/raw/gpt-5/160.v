Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Inductive op :=
| OpAdd
| OpSub
| OpMul
| OpFDiv
| OpPow.

Fixpoint eval_power (base : Z) (ops : list op) (nums : list Z) : Z * list op * list Z :=
  match ops with
  | OpPow :: ops' =>
    match nums with
    | exp :: nums' =>
      let '(vexp, ops'', nums'') := eval_power exp ops' nums' in
      (Z.pow base (Z.to_nat vexp), ops'', nums'')
    | [] => (base, ops, nums)
    end
  | _ => (base, ops, nums)
  end.

Fixpoint eval_muldiv (acc : Z) (ops : list op) (nums : list Z) : Z * list op * list Z :=
  match ops with
  | OpMul :: ops' =>
    match nums with
    | n :: nums' =>
      let '(pn, ops1, nums1) := eval_power n ops' nums' in
      eval_muldiv (acc * pn) ops1 nums1
    | [] => (acc, ops, nums)
    end
  | OpFDiv :: ops' =>
    match nums with
    | n :: nums' =>
      let '(pn, ops1, nums1) := eval_power n ops' nums' in
      eval_muldiv (Z.div acc pn) ops1 nums1
    | [] => (acc, ops, nums)
    end
  | _ => (acc, ops, nums)
  end.

Definition consume_term (n : Z) (ops : list op) (nums : list Z) : Z * list op * list Z :=
  let '(p, ops1, nums1) := eval_power n ops nums in
  eval_muldiv p ops1 nums1.

Fixpoint eval_all (acc : Z) (ops : list op) (nums : list Z) : Z :=
  match ops with
  | [] => acc
  | OpAdd :: ops' =>
    match nums with
    | n :: nums' =>
      let '(t, ops1, nums1) := consume_term n ops' nums' in
      eval_all (acc + t) ops1 nums1
    | [] => acc
    end
  | OpSub :: ops' =>
    match nums with
    | n :: nums' =>
      let '(t, ops1, nums1) := consume_term n ops' nums' in
      eval_all (acc - t) ops1 nums1
    | [] => acc
    end
  | _ => acc
  end.

Definition eval_ops_operands (ops : list op) (nums : list Z) : Z :=
  match nums with
  | [] => 0%Z
  | n0 :: nums' =>
    let '(t0, ops1, nums1) := consume_term n0 ops nums' in
    eval_all t0 ops1 nums1
  end.

Fixpoint div_ok_aux (ops : list op) (nums : list Z) : Prop :=
  match ops, nums with
  | [], _ => True
  | _, [] => True
  | OpFDiv :: ops', n :: nums' =>
    let '(v, ops1, nums1) := eval_power n ops' nums' in
    v <> 0%Z /\ div_ok_aux ops1 nums1
  | _ :: ops', _ :: nums' => div_ok_aux ops' nums'
  end.

Definition do_algebra_spec (operator : list op) (operand : list Z) (result : Z) : Prop :=
  length operand = S (length operator) /\
  operator <> [] /\
  Forall (fun z => (0 <= z)%Z) operand /\
  div_ok_aux operator (tl operand) /\
  result = eval_ops_operands operator operand.