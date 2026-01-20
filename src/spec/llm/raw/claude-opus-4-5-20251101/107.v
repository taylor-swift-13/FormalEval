
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Import ListNotations.

Open Scope Z_scope.

Definition digits (n : Z) : list Z :=
  let fix aux (n : Z) (acc : list Z) (fuel : nat) :=
    match fuel with
    | O => acc
    | S fuel' =>
      if n <=? 0 then acc
      else aux (n / 10) ((n mod 10) :: acc) fuel'
    end
  in aux n [] 100%nat.

Definition is_palindrome (n : Z) : bool :=
  let d := digits n in
  list_eq_dec Z.eq_dec d (rev d).

Definition is_palindrome_prop (n : Z) : Prop :=
  let d := digits n in d = rev d.

Definition is_even (n : Z) : bool :=
  (n mod 2 =? 0).

Definition is_odd (n : Z) : bool :=
  negb (is_even n).

Definition count_even_palindromes (n : Z) : Z :=
  let fix aux (i : Z) (cnt : Z) (fuel : nat) :=
    match fuel with
    | O => cnt
    | S fuel' =>
      if i >? n then cnt
      else if is_palindrome i && is_even i then aux (i + 1) (cnt + 1) fuel'
      else aux (i + 1) cnt fuel'
    end
  in aux 1 0 (Z.to_nat (n + 1)).

Definition count_odd_palindromes (n : Z) : Z :=
  let fix aux (i : Z) (cnt : Z) (fuel : nat) :=
    match fuel with
    | O => cnt
    | S fuel' =>
      if i >? n then cnt
      else if is_palindrome i && is_odd i then aux (i + 1) (cnt + 1) fuel'
      else aux (i + 1) cnt fuel'
    end
  in aux 1 0 (Z.to_nat (n + 1)).

Definition even_odd_palindrome_spec (n : Z) (even_cnt : Z) (odd_cnt : Z) : Prop :=
  n >= 1 /\
  even_cnt = count_even_palindromes n /\
  odd_cnt = count_odd_palindromes n.
