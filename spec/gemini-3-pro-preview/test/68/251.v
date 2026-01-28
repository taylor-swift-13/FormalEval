Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition even_odd_count (l : list Z) : list Z :=
  if existsb (fun x => orb (x <? 0) (x >? 9)) l then
    [0; 0]
  else
    let evens := length (filter Z.even l) in
    let odds := length (filter Z.odd l) in
    [Z.of_nat evens; Z.of_nat odds].

Example test_even_odd_count_2: even_odd_count [0; 7; 2; 3; 6; 8; 10; 2] = [0; 0].
Proof.
  unfold even_odd_count.
  simpl.
  reflexivity.
Qed.