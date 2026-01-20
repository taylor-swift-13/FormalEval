Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint min_prefix (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => 
      match xs with
      | [] => x
      | _ => Z.min x (x + min_prefix xs)
      end
  end.

Fixpoint minSubArraySum (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: xs => 
      match xs with
      | [] => x
      | _ => Z.min (min_prefix (x :: xs)) (minSubArraySum xs)
      end
  end.

Example test_case: minSubArraySum [-1%Z; 2%Z; 4%Z; -50%Z; -5%Z; 6%Z; -7%Z; 8%Z; -9%Z; 10%Z; -7%Z; 10%Z; 2%Z] = -57%Z.
Proof. reflexivity. Qed.