Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Fixpoint fib4n (n : nat) : Z :=
  match n with
  | O => 0%Z
  | S O => 0%Z
  | S (S O) => 2%Z
  | S (S (S O)) => 0%Z
  | S (S (S (S k))) =>
      fib4n (S (S (S k))) + fib4n (S (S k)) + fib4n (S k) + fib4n k
  end.

Definition fib4_spec (n : Z) (res : Z) : Prop :=
  (0 <= n /\ res = fib4n (Z.to_nat n)) \/ (n < 0 /\ res = 0%Z).