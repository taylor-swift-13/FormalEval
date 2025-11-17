（* def add(x: int, y: int):
"""Add two numbers x and y
>>> add(2, 3)
5
>>> add(5, 7)
12
""" *）
(* Pre: no special constraints for `add` *)
Definition Pre (x y : nat) : Prop := True.

Definition add_spec (x : nat) (y : nat) (output : nat) : Prop :=
  output = x + y.