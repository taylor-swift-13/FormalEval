Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Fixpoint count (x : Z) (l : list Z) : nat :=
  match l with
  | [] => 0
  | h :: t => if Z.eq_dec x h then 1 + count x t else count x t
  end.

Fixpoint unique (l : list Z) : list Z :=
  match l with
  | [] => []
  | h :: t => if existsb (fun y => if Z.eq_dec h y then true else false) t
              then unique t
              else h :: unique t
  end.

Definition solution (l : list Z) : Z :=
  let freqs := map (fun x => (x, Z.of_nat (count x l))) (unique l) in
  let min_f := match freqs with
               | [] => 0
               | (_, f) :: _ => fold_right (fun p acc => Z.min (snd p) acc) f freqs
               end in
  let cands := map fst (filter (fun p => Z.eqb (snd p) min_f) freqs) in
  let min_v := match cands with
               | [] => 0
               | h :: t => fold_right Z.min h t
               end in
  min_v * min_f.

Example human_eval_example :
  solution [100000; -50000; 50000; -100000; 100000; -50000; 50000; -100000; 100000; -50000; 50000; -100000; 100000; -50000; -100000; 100000; -50000; 50000; -100000; -100000; 50000] = -250000.
Proof.
  compute. reflexivity.
Qed.