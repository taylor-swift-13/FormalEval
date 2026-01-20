
Require Import List.
Require Import ZArith.
Import ListNotations.

Definition operator := Z -> Z -> Z.

Inductive basic_op : Type :=
| Add
| Sub
| Mul
| Div
| Exp.

Fixpoint apply_op (op : basic_op) (a b : Z) : option Z :=
  match op with
  | Add => Some (a + b)
  | Sub => Some (a - b)
  | Mul => Some (a * b)
  | Div => if b =? 0 then None else Some (a / b) (* integer division *)
  | Exp => if (b <? 0)%Z then None else Some (Z.pow a (Z.to_nat b))
  end.

Fixpoint eval_expression (ops : list basic_op) (operands : list Z) : option Z :=
  match ops, operands with
  | [], [v] => Some v
  | op :: ops', v1 :: v2 :: operands' =>
    match apply_op op v1 v2 with
    | Some res => eval_expression ops' (res :: operands')
    | None => None
    end
  | _, _ => None
  end.

Definition do_algebra_spec (ops : list basic_op) (operands : list Z) (result : Z) : Prop :=
  length ops = length operands - 1 /\
  Forall (fun x => (0 <= x)%Z) operands /\
  length ops >= 1 /\
  length operands >= 2 /\
  eval_expression ops operands = Some result.
