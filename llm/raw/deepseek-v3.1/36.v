
Require Import ZArith.
Require Import List.
Require Import String.
Require Import Ascii.

Fixpoint count_char (c : ascii) (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String h t => (if Ascii.eqb h c then 1 else 0) + count_char c t
  end.

Fixpoint count_sevens_in_string (s : string) : nat :=
  count_char "7"%char s.

Definition fizz_buzz_spec (n : Z) (result : nat) : Prop :=
  let numbers := List.filter (fun i => Z.eqb (Z.modulo i 11) 0 || Z.eqb (Z.modulo i 13) 0) 
                   (List.seq 0 (Z.to_nat n)) in
  result = List.fold_left plus 0 
           (List.map (fun i => count_sevens_in_string (string_of_Z i)) numbers).
