Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint get_digits (n : Z) (fuel : nat) {struct fuel} : list Z :=
  match fuel with
  | 0%nat => []
  | S fuel' => if n <? 10 then [n] else n mod 10 :: get_digits (n / 10) fuel'
  end.

Definition count_odd_digits (l : list Z) : Z :=
  let all_digits := flat_map (fun n => get_digits n 100%nat) l in
  Z.of_nat (length (filter Z.odd all_digits)).

Definition count_even_length_nums (l : list Z) : Z :=
  Z.of_nat (length (filter (fun n => Nat.even (length (get_digits n 100%nat))) l)).

Definition even_odd_count (l : list Z) : list Z :=
  [count_odd_digits l; count_even_length_nums l].

Example test_case : even_odd_count [7; 15; 12; 21; 15; 8; 14] = [8; 5].
Proof.
  reflexivity.
Qed.