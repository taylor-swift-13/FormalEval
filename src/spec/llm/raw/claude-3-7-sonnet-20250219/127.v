
Require Import ZArith.
Open Scope Z_scope.

Definition is_prime (a : Z) : Prop :=
  2 <= a /\
  forall x : Z, 2 <= x <= Z.sqrt a -> a mod x <> 0.

Definition interval := (Z * Z)%type.

Definition intersection_prime_length (interval1 interval2 : interval) (res : string) : Prop :=
  let '(s1, e1) := interval1 in
  let '(s2, e2) := interval2 in
  s1 <= e1 /\
  s2 <= e2 /\
  (exists s3 e3,
      s3 = Z.max s1 s2 /\
      e3 = Z.min e1 e2 /\
      s3 <= e3 /\
      ((res = "YES" /\ is_prime (e3 - s3)) \/ (res = "NO" /\ ~ is_prime (e3 - s3)))) \/
  (Z.max s1 s2 > Z.min e1 e2 /\ res = "NO").
