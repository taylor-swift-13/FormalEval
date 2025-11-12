
Require Import ZArith.
Open Scope Z_scope.

Fixpoint factorial (n : Z) : Z :=
  match n with
  | 0 => 1
  | _ => n * factorial (n - 1)
  end.

Definition special_factorial_spec (n ans : Z) : Prop :=
  n > 0 /\
  ans = 
    (fix aux (i : Z) : Z :=
      if i <? 2 then 1 else factorial i * aux (i - 1)
    ) n.
