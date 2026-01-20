
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.

Open Scope Z_scope.

Fixpoint fibfib_func (n : nat) : Z :=
  match n with
  | O => 0
  | S O => 0
  | S (S O) => 1
  | S (S (S n')) => fibfib_func (S (S n')) + fibfib_func (S n') + fibfib_func n'
  end.

Definition fibfib_spec (n : nat) (result : Z) : Prop :=
  result = fibfib_func n.
