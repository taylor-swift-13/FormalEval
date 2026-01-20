Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Local Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  if existsb (fun x => x <=? 0) l then [0; 0]
  else
    let fix count (l : list Z) (e o : Z) : list Z :=
      match l with
      | [] => [e; o]
      | x :: xs =>
        if x mod 2 =? 0 then count xs (e + 1) o
        else count xs e (o + 1)
      end
    in count l 0 0.

Example test_case_2 : even_odd_count [0%Z; 1%Z; 2%Z; 5%Z; 7%Z; 9%Z; 10%Z] = [0%Z; 0%Z].
Proof. reflexivity. Qed.