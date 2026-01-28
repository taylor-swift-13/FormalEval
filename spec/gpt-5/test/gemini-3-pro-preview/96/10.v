Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix aux (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S fuel' =>
          if i * i >? n then true
          else if (n mod i) =? 0 then false
          else aux (i + 1) fuel'
      end
    in aux 2 (Z.to_nat n).

Fixpoint range_aux (n : nat) (acc : list Z) : list Z :=
  match n with
  | O => acc
  | S n' => range_aux n' (Z.of_nat n' :: acc)
  end.

Definition count_up_to (n : Z) : list Z :=
  let candidates := range_aux (Z.to_nat n) [] in
  filter is_prime candidates.

Example test_count_up_to: count_up_to 101 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73; 79; 83; 89; 97].
Proof. reflexivity. Qed.