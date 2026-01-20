
Require Import ZArith.
Require Import List.
Require Import String.
Open Scope Z_scope.
Open Scope list_scope.

Inductive BinOp : Type :=
  | Add : BinOp
  | Sub : BinOp
  | Mul : BinOp
  | FloorDiv : BinOp
  | Exp : BinOp.

Fixpoint Z_pow (base exp : Z) : Z :=
  match exp with
  | Z0 => 1
  | Zpos p => base * Z_pow base (Z.pred (Zpos p))
  | Zneg _ => 0
  end.

Definition apply_op (op : BinOp) (a b : Z) : Z :=
  match op with
  | Add => a + b
  | Sub => a - b
  | Mul => a * b
  | FloorDiv => Z.div a b
  | Exp => Z_pow a b
  end.

Fixpoint eval_expr (operators : list BinOp) (operands : list Z) : option Z :=
  match operands with
  | nil => None
  | x :: nil => 
      match operators with
      | nil => Some x
      | _ => None
      end
  | x :: rest_operands =>
      match operators with
      | nil => None
      | op :: rest_ops =>
          match eval_expr rest_ops rest_operands with
          | None => None
          | Some result => Some (apply_op op x result)
          end
      end
  end.

Fixpoint build_and_eval (operators : list BinOp) (operands : list Z) (acc : Z) : option Z :=
  match operators, operands with
  | nil, nil => Some acc
  | op :: rest_ops, x :: rest_operands =>
      build_and_eval rest_ops rest_operands (apply_op op acc x)
  | _, _ => None
  end.

Definition do_algebra_spec (operators : list BinOp) (operands : list Z) (result : Z) : Prop :=
  length operators = (length operands - 1)%nat /\
  (length operators >= 1)%nat /\
  (length operands >= 2)%nat /\
  Forall (fun x => x >= 0) operands /\
  match operands with
  | first :: rest => build_and_eval operators rest first = Some result
  | _ => False
  end.
