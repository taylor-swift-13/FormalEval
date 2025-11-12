
Require Import ZArith List String.
Import ListNotations.

Fixpoint sum_digits (l : list Z) : Z :=
  match l with
  | [] => 0
  | h :: t => h + sum_digits t
  end.

Definition signed_digits (n : Z) : list Z :=
  match n with
  | Z0 => [0]
  | Zpos p => 
      let digits := List.map (fun c => Z.of_nat (Nat.of_ascii c - Nat.of_ascii "0"%char)) 
                   (List.rev (List.map Ascii.ascii_of_nat (Nat.to_digits 10 (Pos.to_nat p)))) in
      digits
  | Zneg p => 
      let digits := List.map (fun c => Z.of_nat (Nat.of_ascii c - Nat.of_ascii "0"%char)) 
                   (List.rev (List.map Ascii.ascii_of_nat (Nat.to_digits 10 (Pos.to_nat p)))) in
      match digits with
      | [] => []
      | h :: t => (Z.opp h) :: t
      end
  end.

Definition judge_spec (x : Z) (result : Z) : Prop :=
  result = if Z.gt (sum_digits (signed_digits x)) 0 then 1 else 0.

Definition count_nums_spec (arr : list Z) (count : Z) : Prop :=
  count = List.fold_right Z.add 0 (List.map (fun x => if Z.gt (sum_digits (signed_digits x)) 0 then 1 else 0) arr).
