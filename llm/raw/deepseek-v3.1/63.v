
Require Import ZArith.

Definition fibfib_spec (n : Z) (result : Z) : Prop :=
  match n with
  | 0%Z => result = 0%Z
  | 1%Z => result = 0%Z
  | 2%Z => result = 1%Z
  | _ => exists a b c : Z,
         (forall k : Z, (3%Z <= k <= n)%Z ->
           let (a', b', c') := 
             if k = 3%Z then (0%Z, 0%Z, 1%Z)
             else if k - 1 = n then (b, c, a + b + c)
                  else (b, c, a + b + c)
           in c' = a + b + c) /\
         result = c
  end.
