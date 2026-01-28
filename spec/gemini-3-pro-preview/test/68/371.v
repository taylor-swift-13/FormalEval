Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition solution (l : list Z) : list Z :=
  let rev_l := rev l in
  match rev_l with
  | remaining :: need :: _ =>
      if remaining <? need then [remaining; 0]
      else [need; remaining - need]
  | _ => []
  end.

Example test_case: solution [2%Z; 2%Z; 9%Z; 4%Z; 6%Z; 8%Z; 7%Z; 10%Z; 2%Z] = [2%Z; 0%Z].
Proof. reflexivity. Qed.