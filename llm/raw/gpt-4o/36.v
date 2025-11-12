
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.NArith.NArith.

Definition fizz_buzz_spec (n : nat) (cnt : nat) : Prop :=
  cnt = fold_left Nat.add
    (map (fun i =>
      if (Nat.modulo i 11 =? 0) || (Nat.modulo i 13 =? 0) then
        fold_left Nat.add
          (map (fun c => if c =? "7"%char then 1 else 0) (list_ascii_of_string (string_of_nat i)))
          0
      else 0)
      (seq 0 n))
    0.
