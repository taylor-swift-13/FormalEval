Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_prime (n : Z) : bool :=
  if n <? 2 then false
  else
    let fix check (i : Z) (fuel : nat) : bool :=
      match fuel with
      | O => true
      | S fuel' =>
        if i * i >? n then true
        else if (n mod i) =? 0 then false
        else check (i + 1) fuel'
      end
    in check 2 (Z.to_nat n).

Definition count_up_to (n : Z) : list Z :=
  let fix aux (i : Z) (fuel : nat) : list Z :=
    match fuel with
    | O => []
    | S fuel' =>
      if i <? n then
        if is_prime i then i :: aux (i + 1) fuel'
        else aux (i + 1) fuel'
      else []
    end
  in aux 2 (Z.to_nat n).

Example test_count_up_to_200 : count_up_to 200 = [2; 3; 5; 7; 11; 13; 17; 19; 23; 29; 31; 37; 41; 43; 47; 53; 59; 61; 67; 71; 73; 79; 83; 89; 97; 101; 103; 107; 109; 113; 127; 131; 137; 139; 149; 151; 157; 163; 167; 173; 179; 181; 191; 193; 197; 199].
Proof. reflexivity. Qed.