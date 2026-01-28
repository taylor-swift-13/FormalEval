Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

Fixpoint digits_aux (fuel : nat) (n : Z) : list Z :=
  match fuel with
  | O => []
  | S fuel' =>
      if n <? 10 then [n]
      else (n mod 10) :: digits_aux fuel' (n / 10)
  end.

Definition get_digits (n : Z) : list Z :=
  if n =? 0 then [0]
  else 
    let abs_n := Z.abs n in
    List.rev (digits_aux (Z.to_nat abs_n) abs_n).

Definition sum_signed_digits (n : Z) : Z :=
  match get_digits n with
  | [] => 0
  | hd :: tl =>
      let hd' := if n <? 0 then -hd else hd in
      List.fold_left Z.add tl hd'
  end.

Definition count_nums (l : list Z) : Z :=
  Z.of_nat (List.length (List.filter (fun x => sum_signed_digits x >? 0) l)).

Example test_count_nums: count_nums [11; -12; 93; -125; 10; 121; 109; 93; 11] = 9.
Proof. reflexivity. Qed.