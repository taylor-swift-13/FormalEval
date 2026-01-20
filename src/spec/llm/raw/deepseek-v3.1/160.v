
Require Import List ZArith String.
Import ListNotations.

Inductive algebra_op : Type :=
| Add : algebra_op
| Sub : algebra_op
| Mul : algebra_op
| Div : algebra_op
| Pow : algebra_op.

Definition algebra_op_to_string (op : algebra_op) : string :=
  match op with
  | Add => "+"
  | Sub => "-"
  | Mul => "*"
  | Div => "//"
  | Pow => "**"
  end.

Fixpoint build_expression (operators : list algebra_op) (operands : list Z) : string :=
  match operators, operands with
  | [], [x] => Z.to_string x
  | op::ops, x::xs => Z.to_string x ++ algebra_op_to_string op ++ build_expression ops xs
  | _, _ => ""
  end.

Definition do_algebra_spec (operators : list algebra_op) (operands : list Z) (result : Z) : Prop :=
  length operators = length operands - 1 /\
  length operators >= 1 /\
  length operands >= 2 /\
  (forall x, In x operands -> x >= 0) /\
  result = eval (build_expression operators operands).
