Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Fixpoint even_odd_count_aux (l : list Z) : Z * Z :=
  match l with
  | [] => (0, 0)
  | x :: xs =>
      if x =? 0 then (0, 0)
      else
        let (e, o) := even_odd_count_aux xs in
        if x mod 2 =? 0 then (e + 1, o) else (e, o + 1)
  end.

Definition even_odd_count (l : list Z) : list Z :=
  let (e, o) := even_odd_count_aux l in [e; o].

Example example_new : even_odd_count [0; 2; 4; 6; 8; 10; 1; 3; 5; 33; 7; 9] = [0; 0].
Proof. reflexivity. Qed.